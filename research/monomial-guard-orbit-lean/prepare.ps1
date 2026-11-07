param([string]$LeanBin = '')
$ErrorActionPreference = 'Stop'
$previousLocation = Get-Location
$previousPath = $env:PATH
try {
    Set-Location -LiteralPath $PSScriptRoot
    if ($LeanBin) { $env:PATH = (Resolve-Path -LiteralPath $LeanBin).Path + [IO.Path]::PathSeparator + $env:PATH }
    $folders = @('OrbitGuard','../monomial-guard-ternary-lean/HZ','../monomial-guard-ternary-lean/Ternary')
    $modules = @(Get-ChildItem -LiteralPath $folders -File -Filter '*.lean' |
        ForEach-Object { Get-Content -LiteralPath $_.FullName } |
        ForEach-Object { if ($_ -match '^import (Mathlib\.[A-Za-z0-9_.]+)$') { $Matches[1] } } |
        Sort-Object -Unique)
    if (-not $modules.Count) { throw 'No mathlib imports found.' }
    & lake exe cache get @modules
    if ($LASTEXITCODE -ne 0) { throw 'Dependency preparation failed.' }
} finally {
    Set-Location -LiteralPath $previousLocation.Path
    $env:PATH = $previousPath
}
