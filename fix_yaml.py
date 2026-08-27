import os, re
base_dir = r'c:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = ['euler_polyhedron', 'sylvester_gallai', 'hall_marriage', 'sperners_lemma', 'descartes_rule_of_signs', 'radon_helly']
replacement_text = '''To the maintainers' knowledge, the theorem was not found in an exact declaration name,
    docstring, and type signature search of the pinned Mathlib revision (Mathlib v4.34.0-rc1).'''

for p in packages:
    filepath = os.path.join(base_dir, p, 'formalization.yaml')
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    phrase = r'To the maintainers\' knowledge, the theorem was not found in an exact declaration name,.*?Mathlib v4\.34\.0-rc1\)\.'
    content = re.sub(phrase, '', content, flags=re.DOTALL)
    content = re.sub(r'\n\s*\n\s*\n', '\n\n', content)
    
    lines = content.split('\n')
    new_lines = []
    in_desc = False
    added = False
    for i, line in enumerate(lines):
        if line.startswith('  description: >-'):
            in_desc = True
            new_lines.append(line)
            continue
        
        if in_desc:
            if line.strip() != '' and not line.startswith('    '):
                in_desc = False
                new_lines.append('    ' + replacement_text.replace('\n', '\n    '))
                new_lines.append(line)
                added = True
            else:
                new_lines.append(line)
        else:
            new_lines.append(line)
            
    if in_desc and not added:
        new_lines.append('    ' + replacement_text.replace('\n', '\n    '))
        
    with open(filepath, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(new_lines))
    print(f'Fixed {p}')
