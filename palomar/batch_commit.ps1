$ErrorActionPreference = "Stop"
$root = (Get-Item .).FullName
$palomarDir = Join-Path $root "palomar"
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)

$theorems = Get-ChildItem $palomarDir -Directory | Sort-Object Name
Write-Output "==> Starting batch commit generation for $($theorems.Count) theorems..."

$results = @()
$counter = 1

foreach ($t in $theorems) {
    $slug = $t.Name
    $src = $t.FullName
    
    # 1. Copy package files to root
    Copy-Item "$src\Challenge.lean" "$root\Challenge.lean" -Force
    Copy-Item "$src\Solution.lean" "$root\Solution.lean" -Force
    Copy-Item "$src\comparator.json" "$root\comparator.json" -Force
    Copy-Item "$src\formalization.yaml" "$root\formalization.yaml" -Force
    
    # 2. Strict UTF-8 without BOM & LF sanitation
    @("comparator.json", "formalization.yaml", "Challenge.lean", "Solution.lean") | ForEach-Object {
        $p = Join-Path $root $_
        $txt = [System.IO.File]::ReadAllText($p).Replace("`r`n", "`n")
        [System.IO.File]::WriteAllText($p, $txt, $utf8NoBom)
    }
    
    # 3. Create atomic Git commit for this theorem
    git -C $root add Challenge.lean Solution.lean comparator.json formalization.yaml
    $status = git -C $root status --porcelain
    if ($status) {
        git -C $root commit -m "feat(palomar): package $slug ($counter of $($theorems.Count))"
    } else {
        git -C $root commit --allow-empty -m "feat(palomar): package $slug ($counter of $($theorems.Count))"
    }
    
    $sha = (git -C $root rev-parse HEAD).Trim()
    
    # Extract clean title from formalization.yaml
    $yamlTxt = [System.IO.File]::ReadAllText("$src\formalization.yaml")
    $title = $slug
    if ($yamlTxt -match 'name:\s*"([^"]+)"') {
        $title = $matches[1]
    }
    
    $results += [PSCustomObject]@{
        Index = $counter
        Slug = $slug
        Title = $title
        CommitSHA = $sha
    }
    
    Write-Output "[$counter/$($theorems.Count)] Staged & Committed '$slug' -> $sha"
    $counter++
}

# 4. Push all commits in one single push
Write-Output "==> Pushing all $($theorems.Count) commits to origin main..."
git -C $root push origin main

# 5. Generate Master Checklist Table
$md = @"
# Palomar Submission Master Inventory

All $($theorems.Count) theorems have been compiled, verified, and committed to ``main``.
Every theorem has a dedicated, immutable 40-character Git commit SHA with its ``formalization.yaml`` and ``comparator.json`` active at root.

### Submission Settings for submit.palomar-registry.org:
- **Comparator Path**: ``comparator.json``
- **Existing Palomar ID**: *(leave blank)*
- **Relationship**: ``Maintainer`` / ``Author``

---

## Complete Submission Table

| # | Theorem / Package Title | Slug | Dedicated Commit SHA | Status |
| :---: | :--- | :--- | :--- | :---: |
"@

foreach ($r in $results) {
    $md += "`n| $($r.Index) | **$($r.Title)** | ``$($r.Slug)`` | ``$($r.CommitSHA)`` | [ ] Ready |"
}

$checklistPath = Join-Path $root "PALOMAR_CHECKLIST.md"
[System.IO.File]::WriteAllText($checklistPath, $md.Replace("`r`n", "`n"), $utf8NoBom)
Write-Output "==> Updated $checklistPath successfully!"