import os, re

root = r"c:\Users\x\Documents\antigravity\lean-theorems-1\palomar"

fixed_count = 0

for pkg in sorted(os.listdir(root)):
    yaml_path = os.path.join(root, pkg, "formalization.yaml")
    if os.path.isfile(yaml_path):
        with open(yaml_path, "r", encoding="utf-8", errors="replace") as f:
            txt = f.read()
        
        orig_txt = txt
        
        # 1. Fix classification:: typo
        txt = txt.replace("classification::", "classification:")
        
        # 2. Fix duplicate/stray 34.0-rc1). lines
        lines = []
        for line in txt.splitlines():
            # If line is just stray "34.0-rc1)." or contains stray fragments
            if line.strip() in ["34.0-rc1).", "34.0-rc1). floor(n/3)."]:
                if "floor(n/3)" in line:
                    lines.append("    floor(n/3).")
                continue
            if "34.0-rc1). metric perturbation" in line:
                line = line.replace("34.0-rc1). metric perturbation", "metric perturbation")
            lines.append(line)
        txt = "\n".join(lines) + "\n"
        
        # 3. Fix model designations
        txt = re.sub(r'with Gemini models\b', '', txt)
        txt = re.sub(r'with Claude Opus\b', '', txt)
        txt = re.sub(r'with GPT-4\b', '', txt)
        
        # 4. Standardize tool_setup to model-agnostic text
        txt = txt.replace("checking  under maintainer direction", "checking under maintainer direction")
        
        if txt != orig_txt:
            with open(yaml_path, "w", encoding="utf-8", newline="\n") as f:
                f.write(txt)
            fixed_count += 1
            print(f"Fixed YAML for {pkg}")

print(f"Total YAMLs fixed: {fixed_count}")