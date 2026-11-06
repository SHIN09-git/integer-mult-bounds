param(
    [string]$LeanBin = '',
    [string]$CheckerExe = 'lean4checker'
)

$ErrorActionPreference = 'Stop'
$taskPreviousPath = $env:PATH
$taskPreviousLocation = Get-Location
try {
    Set-Location -LiteralPath $PSScriptRoot
    if ($LeanBin) {
        $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + [IO.Path]::PathSeparator + $env:PATH
    }
    $lakeCommand = Get-Command lake -CommandType Application -ErrorAction Stop
    $leanCommand = Get-Command lean -CommandType Application -ErrorAction Stop
    $checkerCommand = Get-Command $CheckerExe -CommandType Application -ErrorAction Stop
    $leanVersion = & $leanCommand.Source --version
    if ($LASTEXITCODE -ne 0 -or $leanVersion -notmatch '^Lean \(version 4\.24\.0,' -or
        $leanVersion -notmatch '797c613eb9b6d4ec95db23e3e00af9ac6657f24b') {
        throw 'This project requires the pinned Lean 4.24.0 release; see lean-toolchain.'
    }

    $proofFiles = @('HZ.lean', 'Dummy.lean', 'Binary.lean', 'DummyProofCheck.lean', 'Audit.lean', 'lakefile.lean')
    foreach ($directory in @('HZ', 'Dummy', 'Binary')) {
        $proofFiles += @(Get-ChildItem -LiteralPath $directory -Filter '*.lean' -File |
            Sort-Object Name | ForEach-Object { $directory + '/' + $_.Name })
    }
    $forbidden = '\b(sorry|admit|axiom|native_decide|unsafe)\b|set_option\s+.*(?:skipKernel|trustLevel)'
    foreach ($file in $proofFiles) {
        if ((Get-Content -LiteralPath $file -Raw) -match $forbidden) {
            throw ('Forbidden proof construct in ' + $file)
        }
    }

    $inherited = Get-Content -LiteralPath reference/HZ-VERIFICATION.json -Raw | ConvertFrom-Json
    $inheritedCount = 0
    foreach ($property in $inherited.input_sha256.PSObject.Properties) {
        if ($property.Name -eq 'HZ.lean' -or $property.Name.StartsWith('HZ/')) {
            $actual = (Get-FileHash -LiteralPath $property.Name -Algorithm SHA256).Hash.ToLowerInvariant()
            if ($actual -ne $property.Value) { throw ('Inherited proof changed: ' + $property.Name) }
            $inheritedCount++
        }
    }
    if ($inherited.status -ne 'PASS' -or $inheritedCount -ne 7) {
        throw 'Expected seven unchanged HZ sources from the prior verification receipt.'
    }

    $inputs = $proofFiles + @('lean-toolchain', 'lake-manifest.json', 'prepare.ps1', 'verify.ps1',
        'reference/HZ-VERIFICATION.json', 'reference/DUMMY-SOURCE.json', 'reference/TOOLCHAIN.json')
    $hashes = [ordered]@{}
    foreach ($file in $inputs) {
        $hashes[$file] = (Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant()
    }

    $runName = (Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [guid]::NewGuid().ToString('N').Substring(0, 8)
    $runPath = Join-Path (Join-Path $PSScriptRoot '.verification-runs') $runName
    New-Item -ItemType Directory -Path $runPath -Force | Out-Null
    Write-Output ('Checking sources, build and axioms. Logs: ' + $runPath)
    & $lakeCommand.Source build 2>&1 | Tee-Object -FilePath (Join-Path $runPath 'build.log')
    if ($LASTEXITCODE -ne 0) { throw 'Lean compilation failed.' }

    $auditOutput = @(& $lakeCommand.Source env lean -DwarningAsError=true Audit.lean 2>&1)
    $auditOutput | Set-Content -LiteralPath (Join-Path $runPath 'axioms.log') -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw ($auditOutput -join "`n") }
    $reports = [regex]::Matches(($auditOutput -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]')
    if ($reports.Count -ne 28) { throw ('Expected 28 transitive axiom reports, found ' + $reports.Count) }
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($report in $reports) {
        foreach ($name in $report.Groups[1].Value.Split(',')) {
            if ($name.Trim() -and $name.Trim() -notin $allowed) {
                throw ('Unexpected axiom: ' + $name)
            }
        }
    }
    Write-Output 'PASS: seven inherited sources unchanged; 28 transitive axiom reports match the allowlist.'
    Write-Output 'Running fresh kernel replay of DummyProofCheck and all imported dependencies.'
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & $lakeCommand.Source env $checkerCommand.Source --fresh -v DummyProofCheck *> (Join-Path $runPath 'kernel-replay.log')
    if ($LASTEXITCODE -ne 0) {
        Get-Content -LiteralPath (Join-Path $runPath 'kernel-replay.log') -Tail 30
        throw 'Fresh kernel replay failed.'
    }
    $timer.Stop()

    foreach ($file in $inputs) {
        if ((Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant() -ne $hashes[$file]) {
            throw ('Verification input changed during the run: ' + $file)
        }
    }

    [ordered]@{
        status = 'PASS'
        date_utc = [DateTime]::UtcNow.ToString('o')
        lean_version = ($leanVersion -join "`n")
        build_exit_code = 0
        warnings_as_errors = $true
        forbidden_source_construct_matches = 0
        inherited_hz_sources_unchanged = $inheritedCount
        axiom_declarations = 28
        allowed_axioms = $allowed
        unexpected_axioms = @()
        fresh_kernel_replay_exit_code = 0
        fresh_kernel_replay_seconds = $timer.Elapsed.TotalSeconds
        checker_sha256 = (Get-FileHash -LiteralPath $checkerCommand.Source -Algorithm SHA256).Hash.ToLowerInvariant()
        target = 'DummyProofCheck'
        inputs_unchanged_during_verification = $true
        input_sha256 = $hashes
    } | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $runPath 'RESULT.json') -Encoding utf8
    Write-Output ('PASS: build, axiom audit and fresh kernel replay. Logs: ' + $runPath)
} finally {
    $env:PATH = $taskPreviousPath
    Set-Location -LiteralPath $taskPreviousLocation.Path
}

