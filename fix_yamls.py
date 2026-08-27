import yaml
import os
import re

base_dir = r'c:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = ['picks_theorem', 'art_gallery_theorem', 'erdos_szekeres_convex', 'crossing_lemma', 'de_bruijn_erdos']

replacements = {
    'picks_theorem': "discrete formula 2*Area = 2*i + b - 2.",
    'art_gallery_theorem': "floor(n/3).",
    'erdos_szekeres_convex': "verifying the Happy Ending Problem.",
    'crossing_lemma': "e >= 4v edges has at least e^3 / 64v^2 crossings.",
    'de_bruijn_erdos': "metric perturbation proof."
}

disclosure = 'To the maintainers\' knowledge, the theorem was not found in an exact declaration name, docstring, and type signature search of the pinned Mathlib revision (Mathlib v4.34.0-rc1).'

for pkg in packages:
    yaml_path = os.path.join(base_dir, pkg, 'formalization.yaml')
    with open(yaml_path, 'r', encoding='utf-8') as f:
        content = f.read()

    # Find description and chop
    desc_start = content.find('description: >-')
    desc_end = content.find('\n\nclassification:')
    if desc_start != -1 and desc_end != -1:
        desc_block = content[desc_start:desc_end]
        # Remove any existing disclosure strings
        cleaned_desc = re.sub(r'To the maintainers[^.]*\.\s*', '', desc_block).strip()
        
        # Append the replacement if it doesn't already have it
        rep = replacements[pkg]
        if rep not in cleaned_desc:
            cleaned_desc = cleaned_desc.rstrip(', ') + ' ' + rep
        
        cleaned_desc += '\n    ' + disclosure
        
        content = content[:desc_start] + 'description: >-\n    ' + cleaned_desc.split('description: >-')[1].strip().replace('\n', '\n    ') + '\n\nclassification:' + content[desc_end + 16:]
        
    # Check review status
    if 'status: self-assessed' not in content:
        pass # It is already self-assessed in the files
    
    with open(yaml_path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(content)

print("YAML descriptions fixed.")
