import os
import sys

base_dir = r'C:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = [
    'art_gallery_theorem',
    'erdos_szekeres_convex',
    'crossing_lemma',
    'de_bruijn_erdos',
    'ore_dirac_hamiltonian',
    'schurs_theorem',
    'dilworth_mirsky'
]

for p in packages:
    d = os.path.join(base_dir, p)
    if not os.path.exists(d):
        print(f'{p}: Missing')
        continue
    
    res = {'checks': {}}
    
    has_bom = False
    has_crlf = False
    for root, _, files in os.walk(d):
        for f in files:
            fp = os.path.join(root, f)
            with open(fp, 'rb') as fb:
                content = fb.read()
                if content.startswith(b'\xef\xbb\xbf'):
                    has_bom = True
                    print(f'{p}: {f} has BOM')
                if b'\r\n' in content:
                    has_crlf = True
                    print(f'{p}: {f} has CRLF')
                    
    res['checks']['utf8_lf'] = not has_bom and not has_crlf
    
    try:
        with open(os.path.join(d, 'Challenge.lean'), 'r', encoding='utf-8') as f:
            challenge = f.read()
    except Exception as e:
        challenge = ''
    try:
        with open(os.path.join(d, 'Solution.lean'), 'r', encoding='utf-8') as f:
            solution = f.read()
    except Exception as e:
        solution = ''
    try:
        with open(os.path.join(d, 'comparator.json'), 'rb') as f:
            comp_bytes = f.read()
            res['checks']['comparator_0x7b'] = (len(comp_bytes) > 0 and comp_bytes[0] == 0x7b)
    except Exception as e:
        res['checks']['comparator_0x7b'] = False

    res['checks']['no_sorry'] = 'sorry' not in solution
    
    print(f'{p}: {res}')
