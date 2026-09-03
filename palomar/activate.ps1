param (
    [Parameter(Mandatory=$true)]
    [string]$Slug
)

$ErrorActionPreference = "Stop"
$root = "c:\Users\x\Documents\antigravity\lean-theorems-1"
$src = Join-Path "$root\palomar" $Slug

if (!(Test-Path $src)) {
    Write-Error "Theorem slug '$Slug' not found under palomar/. Available slugs:"
    Get-ChildItem "$root\palomar" -Directory | Select-Object -ExpandProperty Name
    exit 1
}

Write-Output "==> Activating theorem package: $Slug"

# Copy package files to root
Copy-Item "$src\Challenge.lean" "$root\Challenge.lean" -Force
Copy-Item "$src\Solution.lean" "$root\Solution.lean" -Force
Copy-Item "$src\comparator.json" "$root\comparator.json" -Force
Copy-Item "$src\formalization.yaml" "$root\formalization.yaml" -Force

# Sanitize UTF-8 without BOM & LF
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)
@("comparator.json", "formalization.yaml", "Challenge.lean", "Solution.lean") | ForEach-Object {
    $p = Join-Path $root $_
    $txt = [System.IO.File]::ReadAllText($p).Replace("`r`n", "`n")
    [System.IO.File]::WriteAllText($p, $txt, $utf8NoBom)
}

# Memory & Process Sanitation for Windows Lean 4 / Lake
$env:LEAN_MEMORY = $null
if (-not $env:LEAN_NUM_THREADS) {
    $env:LEAN_NUM_THREADS = "4"
}
try {
    Get-CimInstance Win32_Process -Filter "Name = 'lean.exe'" -ErrorAction SilentlyContinue | 
        Where-Object { $_.CommandLine -match "--worker" } | 
        ForEach-Object { Stop-Process -Id $_.ProcessId -Force -ErrorAction SilentlyContinue }
} catch { }

Write-Output "==> Running local build verification (lake build Challenge, then Solution)..."
& lake build Challenge
if ($LASTEXITCODE -ne 0) { Write-Error "Lake build failed for Challenge in $Slug!"; exit 1 }
& lake build Solution
if ($LASTEXITCODE -ne 0) { Write-Error "Lake build failed for Solution in $Slug!"; exit 1 }

Write-Output "==> Running automated AST & transitive constant verification..."
& lake env lean --run "$root\palomar\compare.lean"
if ($LASTEXITCODE -ne 0) { Write-Error "Comparator verification failed!"; exit 1 }

Write-Output "==> Committing and pushing to origin main..."
git -C $root add Challenge.lean Solution.lean comparator.json formalization.yaml Formalization/ palomar/
git -C $root commit -m "feat(palomar): activate $Slug for Palomar submission"

$sha = (git -C $root rev-parse HEAD).Trim()

$chkPath = Join-Path $root "PALOMAR_CHECKLIST.md"
if (Test-Path $chkPath) {
    $chk = [System.IO.File]::ReadAllText($chkPath)
    $pattern = '\|\s*(`?[0-9a-f]{40}`?|—)\s*\|\s*`palomar/' + $Slug + '/comparator\.json`'
    $replacement = '| `' + $sha + '` | `palomar/' + $Slug + '/comparator.json`'
    if ([System.Text.RegularExpressions.Regex]::IsMatch($chk, $pattern)) {
        $chk = [System.Text.RegularExpressions.Regex]::Replace($chk, $pattern, $replacement)
        [System.IO.File]::WriteAllText($chkPath, $chk, $utf8NoBom)
        git -C $root add PALOMAR_CHECKLIST.md
        git -C $root commit --amend --no-edit
        $sha = (git -C $root rev-parse HEAD).Trim()
    }
}

git -C $root push origin main --force-with-lease

Write-Output ""
Write-Output "=================================================================="
Write-Output "  SUCCESS: '$Slug' is active and pushed to GitHub!"
Write-Output "=================================================================="
Write-Output "  Repository: sneed-and-feed/lean-theorems-1"
Write-Output "  Commit SHA: $sha"
Write-Output "  Comparator: comparator.json"
Write-Output "  Portal URL: https://submit.palomar-registry.org/"
Write-Output "=================================================================="