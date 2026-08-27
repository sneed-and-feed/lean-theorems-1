import os
import re

base_dir = r'C:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = [
    'art_gallery_theorem', 'erdos_szekeres_convex', 'crossing_lemma', 
    'de_bruijn_erdos', 'ore_dirac_hamiltonian', 'schurs_theorem', 'dilworth_mirsky'
]

for p in packages:
    d = os.path.join(base_dir, p)
    try:
        with open(os.path.join(d, 'Challenge.lean'), 'r', encoding='utf-8') as f:
            content = f.read()
            imports = re.findall(r'^import\s+.*', content, re.MULTILINE)
            print(f'{p}:\n  Imports: {imports}')
            if 'Finset' in content and 'Mathlib.Data.Finset.Card' not in content:
                print(f'  WARNING: Finset used but Card not imported.')
            
        with open(os.path.join(d, 'metadata.yaml'), 'r', encoding='utf-8') as f:
            metadata = f.read()
            print(f'{p} YAML:')
            print('\n'.join('    ' + line for line in metadata.splitlines()[:10])) # print first 10 lines
    except Exception as e:
        print(f'{p}: ERROR {e}')
