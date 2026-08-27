import os, sys

root = r"c:\Users\x\Documents\antigravity\lean-theorems-1"
palomar_dir = os.path.join(root, "palomar")

packages = sorted([d for d in os.listdir(palomar_dir) if os.path.isdir(os.path.join(palomar_dir, d))])
print(f"=== Rigorous Master Audit Across All {len(packages)} Packages ===\n")

for pkg in packages:
    pkg_path = os.path.join(palomar_dir, pkg)
    comp_path = os.path.join(pkg_path, "comparator.json")
    yaml_path = os.path.join(pkg_path, "formalization.yaml")
    chal_path = os.path.join(pkg_path, "Challenge.lean")
    
    issues = []
    
    # 1. BOM check
    if os.path.exists(comp_path):
        with open(comp_path, "rb") as f:
            b = f.read(3)
            if b.startswith(b"\xef\xbb\xbf"):
                issues.append("BOM in comparator.json")
            elif b[0] != 123:
                issues.append(f"first byte {b[0]} != 123")
    else:
        issues.append("missing comparator.json")
        
    # 2. YAML check
    if os.path.exists(yaml_path):
        with open(yaml_path, "r", encoding="utf-8", errors="replace") as f:
            ytxt = f.read()
        if "classification::" in ytxt:
            issues.append("YAML classification:: typo")
        if "34.0-rc1)." in ytxt:
            issues.append("YAML stray '34.0-rc1).' text")
    else:
        issues.append("missing formalization.yaml")
        
    # 3. Check Challenge.lean content
    if os.path.exists(chal_path):
        with open(chal_path, "r", encoding="utf-8", errors="replace") as f:
            ctxt = f.read()
        if "inductive PlanarMap" in ctxt:
            issues.append("Anti-Pattern: inductive PlanarMap counter")
        if "structure LatticeTriangulation" in ctxt:
            issues.append("Anti-Pattern: synthetic LatticeTriangulation")
    else:
        issues.append("missing Challenge.lean")
        
    if issues:
        print(f"❌ {pkg}: {', '.join(issues)}")
    else:
        print(f"✅ {pkg}: Clean")