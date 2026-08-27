import os
import re
import subprocess
import yaml

base_dir = r'C:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = [
    'art_gallery_theorem', 'erdos_szekeres_convex', 'crossing_lemma', 
    'de_bruijn_erdos', 'ore_dirac_hamiltonian', 'schurs_theorem', 'dilworth_mirsky'
]

results = {}

for p in packages:
    print(f"--- Auditing {p} ---")
    d = os.path.join(base_dir, p)
    
    # 1. Yaml checks
    yaml_path = os.path.join(d, 'formalization.yaml')
    try:
        with open(yaml_path, 'r', encoding='utf-8') as f:
            meta = yaml.safe_load(f)
            rel = meta.get('relationships', [])
            rel_types = [r.get('type') for r in rel]
            valid_types = {'formalizes', 'adapts', 'background', 'independently-proves'}
            invalid = [t for t in rel_types if t not in valid_types]
            if invalid:
                print(f"  YAML ERROR: Invalid relationship types: {invalid}")
            
            # Check scope limitations
            scope = meta.get('scope_limitations', '')
            if not scope and not meta.get('disclosures'):
                print(f"  YAML WARNING: No scope limitations disclosed?")
    except Exception as e:
        print(f"  YAML READ ERROR: {e}")

    # 2. Compile Challenge.lean
    chal_path = os.path.join(d, 'Challenge.lean')
    res = subprocess.run(['lake', 'env', 'lean', chal_path], cwd=r'C:\Users\x\Documents\antigravity\lean-theorems-1', capture_output=True, text=True)
    if res.returncode != 0:
        print(f"  COMPILE ERROR:\n{res.stderr.strip()}")
    else:
        print(f"  COMPILE OK")
        
    # 3. Check for fake inductives or tautologies
    try:
        with open(chal_path, 'r', encoding='utf-8') as f:
            content = f.read()
            if 'inductive' in content and 'Counter' in content:
                print(f"  TAUTOLOGY WARNING: Found 'inductive' and 'Counter'")
    except Exception as e:
        print(f"  READ ERROR: {e}")
