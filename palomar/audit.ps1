param (
    [Parameter(Mandatory=$true)]
    [string]$Slug
)

$ErrorActionPreference = "Stop"
$root = (Get-Item $PSScriptRoot).Parent.FullName
$src = Join-Path "$root\palomar" $Slug

if (!(Test-Path $src)) {
    Write-Error "Theorem slug '$Slug' not found under palomar/. Available slugs:"
    Get-ChildItem "$root\palomar" -Directory | Select-Object -ExpandProperty Name
    exit 1
}

# Memory & Process Sanitation for Windows Lean 4 / Lake
# 1. Unset restrictive LEAN_MEMORY caps that cause out-of-memory panics & olean read failures
$env:LEAN_MEMORY = $null
if (-not $env:LEAN_NUM_THREADS) {
    $env:LEAN_NUM_THREADS = "4"
}

# 2. Prune lingering lean.exe LSP worker processes to free virtual memory commit limit
try {
    Get-CimInstance Win32_Process -Filter "Name = 'lean.exe'" -ErrorAction SilentlyContinue | 
        Where-Object { $_.CommandLine -match "--worker" } | 
        ForEach-Object { Stop-Process -Id $_.ProcessId -Force -ErrorAction SilentlyContinue }
} catch { }

$utf8NoBom = New-Object System.Text.UTF8Encoding($false)

Write-Host "====================================================" -ForegroundColor Cyan
Write-Host "  PRE-FLIGHT AUDIT: $Slug" -ForegroundColor Cyan
Write-Host "====================================================" -ForegroundColor Cyan

# 1. Encoding & BOM Check (First byte of comparator.json must be 0x7B '{')
$compPath = "$src\comparator.json"
if (!(Test-Path $compPath)) {
    Write-Host "[BLOCKING FAIL] Missing comparator.json in $src" -ForegroundColor Red
    exit 1
}
$bytes = [System.IO.File]::ReadAllBytes($compPath)
if ($bytes.Length -eq 0 -or $bytes[0] -ne 123) {
    Write-Host "[BLOCKING FAIL] comparator.json has BOM or invalid start byte ($($bytes[0]))" -ForegroundColor Red
    exit 1
}
Write-Host "[PASS] Strict UTF-8 without BOM (First byte: 0x7B)" -ForegroundColor Green

# 2. Line Ending Sanitization (CRLF -> LF across all 4 package files)
@("comparator.json", "formalization.yaml", "Challenge.lean", "Solution.lean") | ForEach-Object {
    $p = Join-Path $src $_
    if (Test-Path $p) {
        $txt = [System.IO.File]::ReadAllText($p).Replace("`r`n", "`n")
        [System.IO.File]::WriteAllText($p, $txt, $utf8NoBom)
    }
}
Write-Host "[PASS] Normalized Unix LF line endings without BOM" -ForegroundColor Green

# 3. Sandbox Hermeticity Check (Challenge.lean must only import Mathlib)
$chalPath = "$src\Challenge.lean"
if (Test-Path $chalPath) {
    $chalLines = Get-Content $chalPath
    $badImports = $chalLines | Where-Object { $_ -match "^\s*import\s+" -and $_ -notmatch "^\s*import\s+Mathlib" }
    if ($badImports) {
        Write-Host "[BLOCKING FAIL] Challenge.lean imports non-Mathlib modules: $badImports" -ForegroundColor Red
        exit 1
    }
    Write-Host "[PASS] Standalone Challenge.lean hermeticity verified" -ForegroundColor Green
}

# 4. Axiom and Sorry Check in Solution.lean
$solPath = "$src\Solution.lean"
if (Test-Path $solPath) {
    $solTxt = [System.IO.File]::ReadAllText($solPath)
    if ($solTxt -match "\bsorry\b" -or $solTxt -match "\baxiom\b") {
        Write-Host "[BLOCKING FAIL] Solution.lean contains 'sorry' or custom 'axiom'" -ForegroundColor Red
        exit 1
    }
    Write-Host "[PASS] Zero sorries and zero custom axioms in Solution.lean" -ForegroundColor Green
}

# 5. Schema Check in formalization.yaml
$yamlPath = "$src\formalization.yaml"
if (Test-Path $yamlPath) {
    $yamlTxt = [System.IO.File]::ReadAllText($yamlPath)
    if ($yamlTxt -notmatch "version:\s*`"v0.4`"") {
        Write-Host "[NON-BLOCKING WARNING] formalization.yaml schema is not v0.4" -ForegroundColor Yellow
    } else {
        Write-Host "[PASS] formalization.yaml v0.4 schema verified" -ForegroundColor Green
    }
}

# 6. Sequential Lake Build Check (-j 2)
Copy-Item "$src\Challenge.lean" "$root\Challenge.lean" -Force
Copy-Item "$src\Solution.lean" "$root\Solution.lean" -Force
Copy-Item "$src\comparator.json" "$root\comparator.json" -Force
Copy-Item "$src\formalization.yaml" "$root\formalization.yaml" -Force

Write-Host "==> Running sequential build check (LEAN_NUM_THREADS=$($env:LEAN_NUM_THREADS), LEAN_MEMORY=default)..." -ForegroundColor Cyan
& lake build Challenge
if ($LASTEXITCODE -ne 0) { Write-Error "Build failed for Challenge!"; exit 1 }
& lake build Solution
if ($LASTEXITCODE -ne 0) { Write-Error "Build failed for Solution!"; exit 1 }

# 7. Automated AST Comparator Verification (AP-20 & AP-31)
Write-Host "==> Running automated AST expression comparator verification..." -ForegroundColor Cyan
& lake env lean --run "$root\palomar\compare.lean"
if ($LASTEXITCODE -ne 0) { Write-Error "Comparator AST expression mismatch detected!"; exit 1 }

Write-Host ""
Write-Host "====================================================" -ForegroundColor Green
Write-Host "  AUDIT SUCCESS: No blocking findings for '$Slug'" -ForegroundColor Green
Write-Host "====================================================" -ForegroundColor Green