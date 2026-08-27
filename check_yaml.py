import os

root = r"c:\Users\x\Documents\antigravity\lean-theorems-1\palomar"

for pkg in sorted(os.listdir(root)):
    yaml_path = os.path.join(root, pkg, "formalization.yaml")
    if os.path.exists(yaml_path):
        with open(yaml_path, "r", encoding="utf-8", errors="replace") as f:
            lines = f.readlines()
        for i, line in enumerate(lines):
            if "34.0-rc1" in line:
                if line.count("34.0-rc1") > 1 or "34.0-rc1)." in line and not line.strip().endswith("(Mathlib v4.34.0-rc1)."):
                    print(f"DUPLICATE in {pkg}:{i+1}: {line.strip()}")