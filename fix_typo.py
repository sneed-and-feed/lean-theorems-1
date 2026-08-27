import os
import re

base_dir = r'C:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = [
    'art_gallery_theorem', 'erdos_szekeres_convex', 'crossing_lemma', 
    'de_bruijn_erdos', 'ore_dirac_hamiltonian', 'schurs_theorem', 'dilworth_mirsky'
]

for p in packages:
    yaml_path = os.path.join(base_dir, p, 'formalization.yaml')
    with open(yaml_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    content = content.replace('Mathlib v4.classification:', 'Mathlib v4.34.0-rc1).\n\nclassification:')
    
    with open(yaml_path, 'w', encoding='utf-8') as f:
        f.write(content)

print('Fixed Mathlib v4 classification bug')
