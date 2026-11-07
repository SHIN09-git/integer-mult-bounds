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

    $proofFiles = @('HZ.lean', 'Dummy.lean', 'Binary.lean', 'GuardDP.lean', 'DPProofCheck.lean',
        'Audit.lean', 'Examples.lean', 'lakefile.lean')
    foreach ($directory in @('HZ', 'Dummy', 'Binary', 'GuardDP')) {
        $proofFiles += @(Get-ChildItem -LiteralPath $directory -Filter '*.lean' -File |
            Sort-Object Name | ForEach-Object { $directory + '/' + $_.Name })
    }
    $forbidden = '\b(sorry|admit|axiom|native_decide|unsafe)\b|set_option\s+.*(?:skipKernel|trustLevel)'
    foreach ($file in $proofFiles) {
        if ((Get-Content -LiteralPath $file -Raw) -match $forbidden) {
            throw ('Forbidden proof construct in ' + $file)
        }
    }

    $inherited = Get-Content -LiteralPath reference/PREVIOUS-RESULT.json -Raw | ConvertFrom-Json
    $inheritedCount = 0
    foreach ($property in $inherited.input_sha256.PSObject.Properties) {
        if ($property.Name -match '^(HZ|Dummy|Binary)(\.lean$|/)') {
            $actual = (Get-FileHash -LiteralPath $property.Name -Algorithm SHA256).Hash.ToLowerInvariant()
            if ($actual -ne $property.Value) { throw ('Inherited proof changed: ' + $property.Name) }
            $inheritedCount++
        }
    }
    if ($inherited.status -ne 'PASS' -or $inheritedCount -ne 15) {
        throw 'Expected 15 unchanged HZ, Dummy and Binary sources from the previous receipt.'
    }

    $inputs = $proofFiles + @('lean-toolchain', 'lake-manifest.json', 'prepare.ps1', 'verify.ps1',
        'reference/PREVIOUS-RESULT.json', 'reference/TOOLCHAIN.json', 'reference/ALGORITHM.md')
    $hashes = [ordered]@{}
    foreach ($file in $inputs) {
        $hashes[$file] = (Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant()
    }

    $runName = (Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [guid]::NewGuid().ToString('N').Substring(0, 8)
    $runPath = Join-Path (Join-Path $PSScriptRoot '.verification-runs') $runName
    New-Item -ItemType Directory -Path $runPath -Force | Out-Null
    $manifest = Get-Content -LiteralPath lake-manifest.json -Raw | ConvertFrom-Json
    $packages = foreach ($package in $manifest.packages) {
        $packageDir = Join-Path $manifest.packagesDir $package.name
        $revision = & git -C $packageDir rev-parse HEAD
        if ($LASTEXITCODE -ne 0 -or $revision -ne $package.rev) { throw ('Wrong dependency revision: ' + $package.name) }
        $changes = @(& git -C $packageDir status --porcelain --untracked-files=no)
        if ($LASTEXITCODE -ne 0 -or $changes.Count) { throw ('Modified dependency: ' + $package.name) }
        [ordered]@{ name = $package.name; commit = $revision; tracked_changes = 0 }
    }
    $packages | ConvertTo-Json | Set-Content -LiteralPath (Join-Path $runPath 'dependencies.json') -Encoding utf8
    Write-Output ('Checking sources, build, examples and axioms. Logs: ' + $runPath)
    & $lakeCommand.Source build 2>&1 | Tee-Object -FilePath (Join-Path $runPath 'build.log')
    if ($LASTEXITCODE -ne 0) { throw 'Lean compilation failed.' }

    & $lakeCommand.Source env lean -DwarningAsError=true Examples.lean *> (Join-Path $runPath 'examples.log')
    if ($LASTEXITCODE -ne 0) { throw 'Executable witness replay failed.' }

    $auditOutput = @(& $lakeCommand.Source env lean -DwarningAsError=true Audit.lean 2>&1)
    $auditOutput | Set-Content -LiteralPath (Join-Path $runPath 'axioms.log') -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw ($auditOutput -join "`n") }
    $reports = [regex]::Matches(($auditOutput -join "`n"), "'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
    $expected = @(Get-Content -LiteralPath Audit.lean | ForEach-Object {
        if ($_ -match '^#print axioms (\S+)$') { $Matches[1] }
    })
    $reported = @($reports | ForEach-Object { $_.Groups[1].Value })
    if ($expected.Count -ne 25 -or $reports.Count -ne 25 -or (Compare-Object $expected $reported)) {
        throw 'Incomplete or unexpected transitive axiom reports.'
    }
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($report in $reports) {
        foreach ($name in $report.Groups[2].Value.Split(',')) {
            if ($name.Trim() -and $name.Trim() -notin $allowed) {
                throw ('Unexpected axiom: ' + $name)
            }
        }
    }
    Write-Output 'PASS: 15 inherited sources, executable examples and 25 transitive axiom reports.'
    Write-Output 'Running fresh kernel replay of DPProofCheck and all imported dependencies.'
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & $lakeCommand.Source env $checkerCommand.Source --fresh -v DPProofCheck *> (Join-Path $runPath 'kernel-replay.log')
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
        inherited_sources_unchanged = $inheritedCount
        executable_examples_exit_code = 0
        axiom_declarations = $reports.Count
        allowed_axioms = $allowed
        unexpected_axioms = @()
        fresh_kernel_replay_exit_code = 0
        fresh_kernel_replay_seconds = $timer.Elapsed.TotalSeconds
        checker_sha256 = (Get-FileHash -LiteralPath $checkerCommand.Source -Algorithm SHA256).Hash.ToLowerInvariant()
        target = 'DPProofCheck'
        inputs_unchanged_during_verification = $true
        input_sha256 = $hashes
    } | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $runPath 'RESULT.json') -Encoding utf8
    Write-Output ('PASS: build, axiom audit and fresh kernel replay. Logs: ' + $runPath)
} finally {
    $env:PATH = $taskPreviousPath
    Set-Location -LiteralPath $taskPreviousLocation.Path
}

