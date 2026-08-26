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

Write-Output "==> Running local build verification (lake build Challenge Solution)..."
& lake build Challenge Solution

if ($LASTEXITCODE -ne 0) {
    Write-Error "Lake build failed for $Slug!"
    exit 1
}

Write-Output "==> Committing and pushing to origin main..."
git -C $root add Challenge.lean Solution.lean comparator.json formalization.yaml
git -C $root commit -m "feat(palomar): activate $Slug for Palomar submission"
git -C $root push origin main

$sha = (git -C $root rev-parse HEAD).Trim()

Write-Output ""
Write-Output "=================================================================="
Write-Output "  SUCCESS: '$Slug' is active and pushed to GitHub!"
Write-Output "=================================================================="
Write-Output "  Repository: sneed-and-feed/lean-theorems-1"
Write-Output "  Commit SHA: $sha"
Write-Output "  Comparator: comparator.json"
Write-Output "  Portal URL: https://submit.palomar-registry.org/"
Write-Output "=================================================================="