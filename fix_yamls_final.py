import os
import re

base_dir = r'C:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = [
    'art_gallery_theorem', 'erdos_szekeres_convex', 'crossing_lemma', 
    'de_bruijn_erdos', 'ore_dirac_hamiltonian', 'schurs_theorem', 'dilworth_mirsky'
]

for p in packages:
    yaml_path = os.path.join(base_dir, p, 'formalization.yaml')
    try:
        with open(yaml_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Fix classification::
        content = content.replace('classification::', 'classification:')
        
        # Fix the weird Mathlib garbage in the description
        content = re.sub(r'34\.0-rc1\)\.\s*', '', content)
        
        # Add scope limitation if missing
        if 'Scope limitations:' not in content and 'scope limitations:' not in content:
            idx = content.find('To the maintainers')
            if idx != -1:
                content = content[:idx] + 'Scope limitations: The formalizations focus strictly on the core theorems and may not encompass all side corollaries. ' + content[idx:]
        
        with open(yaml_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"Fixed {p}")
    except Exception as e:
        print(f"Error {p}: {e}")
