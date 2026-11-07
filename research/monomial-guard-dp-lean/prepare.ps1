param([string]$LeanBin = '')
$ErrorActionPreference = 'Stop'
$taskPreviousPath = $env:PATH
$taskPreviousLocation = Get-Location
try {
    Set-Location -LiteralPath $PSScriptRoot
    if ($LeanBin) {
        $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + [IO.Path]::PathSeparator + $env:PATH
    }
    $modules = @(Get-ChildItem -LiteralPath HZ,Dummy,Binary,GuardDP -Filter '*.lean' -File |
        ForEach-Object { Get-Content -LiteralPath $_.FullName } |
        ForEach-Object { if ($_ -match '^import (Mathlib\.[A-Za-z0-9_.]+)$') { $Matches[1] } } |
        Sort-Object -Unique)
    if (-not $modules.Count) { throw 'No mathlib imports found.' }
    & lake exe cache get @modules
    if ($LASTEXITCODE -ne 0) { throw 'Dependency preparation failed.' }
} finally {
    $env:PATH = $taskPreviousPath
    Set-Location -LiteralPath $taskPreviousLocation.Path
}

