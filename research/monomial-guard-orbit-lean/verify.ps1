param([string]$LeanBin = '', [string]$CheckerExe = 'lean4checker')
$ErrorActionPreference = 'Stop'
$previousLocation = Get-Location
$previousPath = $env:PATH
function Get-InputHash([string]$file) {
    (Get-FileHash -LiteralPath $file -Algorithm SHA256).Hash.ToLowerInvariant()
}
$parents = [ordered]@{
    integerMultTernary = @{dir='../monomial-guard-ternary-lean'; count=27; hash='f8abbcfdd58bc43c10bd4dc50dd6bb16ce628475eb8dcfa6883f853ba0b9de7b'}
}
function Test-Parents {
    foreach ($p in $parents.Values) {
        $receipt = Join-Path $p.dir 'verification/RESULT.json'
        if ((Get-InputHash $receipt) -ne $p.hash) { throw ('Predecessor receipt changed: ' + $p.dir) }
        $prior = Get-Content -Raw -LiteralPath $receipt | ConvertFrom-Json
        $items = @($prior.input_sha256.PSObject.Properties)
        if ($prior.status -ne 'PASS' -or $items.Count -ne $p.count) { throw ('Incomplete predecessor: ' + $p.dir) }
        foreach ($item in $items) {
            if ((Get-InputHash (Join-Path $p.dir $item.Name)) -ne $item.Value) {
                throw ('Changed predecessor input: ' + $p.dir + '/' + $item.Name)
            }
        }
    }
}
try {
    Set-Location -LiteralPath $PSScriptRoot
    if ($LeanBin) { $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + [IO.Path]::PathSeparator + $env:PATH }
    $checker = (Get-Command $CheckerExe -CommandType Application).Source
    $version = & lean --version
    if ($LASTEXITCODE -ne 0 -or $version -notmatch '^Lean \(version 4\.24\.0,' -or
        $version -notmatch '797c613eb9b6d4ec95db23e3e00af9ac6657f24b') { throw 'Unexpected Lean toolchain.' }
    $sources = @('lakefile.lean','OrbitGuard.lean','OrbitProofCheck.lean','Audit.lean','Examples.lean') +
        @(Get-ChildItem OrbitGuard -File -Filter '*.lean' | Sort-Object Name | ForEach-Object { 'OrbitGuard/' + $_.Name })
    $inputs = $sources + @('lean-toolchain','lake-manifest.json','prepare.ps1','verify.ps1')
    $hashes = [ordered]@{}
    foreach ($file in $inputs) { $hashes[$file] = Get-InputHash $file }
    foreach ($file in $sources) {
        if ((Get-Content -Raw -LiteralPath $file) -match '\b(sorry|admit|axiom|native_decide|unsafe)\b|set_option\s+.*(?:skipKernel|trustLevel)') {
            throw ('Forbidden proof construct in ' + $file)
        }
    }
    Test-Parents
    $run = Join-Path '.verification-runs' ((Get-Date -Format 'yyyyMMdd-HHmmss') + '-' + [guid]::NewGuid().ToString('N').Substring(0,8))
    New-Item -ItemType Directory -Path $run | Out-Null
    $manifest = Get-Content -Raw -LiteralPath lake-manifest.json | ConvertFrom-Json
    $localPackages = @($manifest.packages | Where-Object type -eq 'path' | ForEach-Object name)
    if (Compare-Object @($parents.Keys) $localPackages) { throw 'Unexpected set of local dependencies.' }
    $packages = foreach ($pkg in $manifest.packages) {
        if ($pkg.type -eq 'path') {
            $p = $parents[$pkg.name]
            if ((Resolve-Path -LiteralPath $pkg.dir).Path -ne (Resolve-Path -LiteralPath $p.dir).Path) { throw 'Unexpected local path.' }
            [ordered]@{name=$pkg.name; path=$pkg.dir; receipt_sha256=$p.hash; verified_inputs=$p.count}
            continue
        }
        if ($pkg.type -ne 'git') { throw ('Unexpected dependency: ' + $pkg.name) }
        $dir = Join-Path $manifest.packagesDir $pkg.name
        $rev = & git -C $dir rev-parse HEAD
        if ($LASTEXITCODE -ne 0 -or $rev -ne $pkg.rev) { throw ('Wrong revision for ' + $pkg.name) }
        $changes = @(& git -C $dir status --porcelain --untracked-files=no)
        if ($LASTEXITCODE -ne 0 -or $changes.Count) { throw ('Modified dependency: ' + $pkg.name) }
        [ordered]@{name=$pkg.name; commit=$rev; tracked_changes=0}
    }
    $packages | ConvertTo-Json | Set-Content -LiteralPath "$run/dependencies.json" -Encoding utf8
    Write-Output ('Verifying ' + $run)
    & lake build 2>&1 | Tee-Object -FilePath "$run/build.log"
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
    & lake env lean -DwarningAsError=true Examples.lean *> "$run/examples.log"
    if ($LASTEXITCODE -ne 0) { throw 'Executable examples failed.' }
    $examples = @(Get-Content -LiteralPath "$run/examples.log" | Where-Object { $_ -match '^PASS ' })
    if ($examples.Count -ne 8) { throw 'Expected eight executable check groups.' }
    $audit = @(& lake env lean -DwarningAsError=true Audit.lean 2>&1)
    $audit | Set-Content -LiteralPath "$run/axioms.log" -Encoding utf8
    if ($LASTEXITCODE -ne 0) { throw 'Axiom audit failed.' }
    $reports = [regex]::Matches(($audit -join [Environment]::NewLine), "'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
    $expected = @(Get-Content Audit.lean | ForEach-Object { if ($_ -match '^#print axioms (\S+)$') { $Matches[1] } })
    $reported = @($reports | ForEach-Object { $_.Groups[1].Value })
    if ($expected.Count -ne 37 -or $reported.Count -ne 37 -or (Compare-Object $expected $reported)) {
        throw 'Expected 37 named axiom reports.'
    }
    $allowed = @('propext','Classical.choice','Quot.sound')
    foreach ($report in $reports) {
        foreach ($name in $report.Groups[2].Value.Split(',')) {
            if ($name.Trim() -and $name.Trim() -notin $allowed) { throw ('Unexpected axiom: ' + $name) }
        }
    }
    Write-Output 'Eight executable checks and 37 axiom reports passed. Starting fresh kernel replay.'
    $timer = [Diagnostics.Stopwatch]::StartNew()
    & lake env $checker --fresh -v OrbitProofCheck *> "$run/kernel-replay.log"
    if ($LASTEXITCODE -ne 0) { throw 'Fresh kernel replay failed.' }
    $timer.Stop()
    Test-Parents
    foreach ($file in $inputs) {
        if ((Get-InputHash $file) -ne $hashes[$file]) { throw ('Input changed during verification: ' + $file) }
    }
    [ordered]@{
        status='PASS'; target='OrbitProofCheck'; date_utc=[DateTime]::UtcNow.ToString('o')
        lean_version=($version -join [Environment]::NewLine); build_exit_code=0; warnings_as_errors=$true
        executable_examples_exit_code=0; executable_example_groups=$examples.Count; axiom_declarations=$reported.Count
        allowed_axioms=$allowed; unexpected_axioms=@(); forbidden_source_construct_matches=0
        fresh_kernel_replay_exit_code=0; fresh_kernel_replay_seconds=$timer.Elapsed.TotalSeconds
        checker_sha256=(Get-InputHash $checker); predecessor_packages=$parents
        inputs_unchanged_during_verification=$true; input_sha256=$hashes
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath "$run/RESULT.json" -Encoding utf8
    Write-Output ('PASS. Receipt: ' + "$run/RESULT.json")
} finally {
    Set-Location -LiteralPath $previousLocation.Path
    $env:PATH = $previousPath
}
