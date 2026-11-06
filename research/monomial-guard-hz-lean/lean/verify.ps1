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
    if ($LASTEXITCODE -ne 0 -or $leanVersion -notmatch '^Lean \(version 4\.24\.0,') {
        throw 'This project requires Lean 4.24.0; see lean-toolchain.'
    }

    $proofFiles = @('HZ.lean', 'ProofCheck.lean', 'Audit.lean', 'lakefile.lean') +
        @(Get-ChildItem -LiteralPath HZ -Filter '*.lean' -File | ForEach-Object { 'HZ/' + $_.Name })
    $forbidden = '\b(sorry|admit|axiom|native_decide|unsafe)\b|set_option\s+.*(?:skipKernel|trustLevel)'
    foreach ($file in $proofFiles) {
        if ((Get-Content -LiteralPath $file -Raw) -match $forbidden) {
            throw ('Forbidden proof construct in ' + $file)
        }
    }

    $runName = (Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [guid]::NewGuid().ToString('N').Substring(0, 8)
    $runPath = Join-Path (Join-Path $PSScriptRoot '.verification-runs') $runName
    New-Item -ItemType Directory -Path $runPath -Force | Out-Null
    & $lakeCommand.Source build 2>&1 | Tee-Object -FilePath (Join-Path $runPath 'build.log')
    if ($LASTEXITCODE -ne 0) { throw 'Lean compilation failed.' }

    $auditOutput = @(& $lakeCommand.Source env lean -DwarningAsError=true Audit.lean 2>&1)
    if ($LASTEXITCODE -ne 0) { throw ($auditOutput -join "`n") }
    $auditOutput | Set-Content -LiteralPath (Join-Path $runPath 'axioms.log') -Encoding utf8
    $reports = [regex]::Matches(($auditOutput -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]')
    if ($reports.Count -ne 22) { throw 'Expected 22 transitive axiom reports.' }
    $allowed = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($report in $reports) {
        foreach ($name in $report.Groups[1].Value.Split(',')) {
            if ($name.Trim() -and $name.Trim() -notin $allowed) {
                throw ('Unexpected axiom: ' + $name)
            }
        }
    }
    Write-Output 'PASS: 22 transitive axiom reports match the allowlist.'
    Write-Output 'Running fresh kernel replay of ProofCheck and all imported dependencies.'
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & $lakeCommand.Source env $checkerCommand.Source --fresh -v ProofCheck 2>&1 |
        Tee-Object -FilePath (Join-Path $runPath 'kernel-replay.log')
    if ($LASTEXITCODE -ne 0) { throw 'Fresh kernel replay failed.' }
    $timer.Stop()

    $hashes = [ordered]@{}
    foreach ($file in ($proofFiles + @('lean-toolchain', 'lake-manifest.json'))) {
        $hashes[$file] = (Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant()
    }
    [ordered]@{
        status = 'PASS'
        date_utc = [DateTime]::UtcNow.ToString('o')
        lean_version = ($leanVersion -join "`n")
        build_exit_code = 0
        warnings_as_errors = $true
        forbidden_source_construct_matches = 0
        axiom_declarations = 22
        allowed_axioms = $allowed
        unexpected_axioms = @()
        fresh_kernel_replay_exit_code = 0
        fresh_kernel_replay_seconds = $timer.Elapsed.TotalSeconds
        checker_sha256 = (Get-FileHash -LiteralPath $checkerCommand.Source -Algorithm SHA256).Hash.ToLowerInvariant()
        target = 'ProofCheck'
        input_sha256 = $hashes
    } | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $runPath 'RESULT.json') -Encoding utf8
    Write-Output ('PASS: build, axiom audit and fresh kernel replay. Logs: ' + $runPath)
} finally {
    $env:PATH = $taskPreviousPath
    Set-Location -LiteralPath $taskPreviousLocation.Path
}
