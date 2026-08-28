import os, json

base_dir = r'c:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = ['radon_helly', 'schurs_theorem', 'frankl_wilson', 'kneser_lovasz', 'ore_dirac_hamiltonian']
files = ['comparator.json', 'formalization.yaml', 'Challenge.lean', 'Solution.lean']

for pkg in packages:
    pkg_dir = os.path.join(base_dir, pkg)
    print(f'=== {pkg} ===')
    
    # Check BOM, CRLF, size for each file
    for fname in files:
        fpath = os.path.join(pkg_dir, fname)
        if not os.path.exists(fpath):
            print(f'  [MISSING] {fname}')
            continue
        with open(fpath, 'rb') as f:
            content = f.read()
        has_bom = content.startswith(b'\xef\xbb\xbf')
        has_crlf = b'\r\n' in content or b'\r' in content
        first_byte = f'0x{content[0]:02X}' if content else '0x00'
        if has_bom or has_crlf:
            print(f'  [FAIL] {fname}: BOM={has_bom}, CRLF={has_crlf}, FirstByte={first_byte}')
        else:
            print(f'  [PASS] {fname}: UTF-8 without BOM, LF only, FirstByte={first_byte}')

    # Check comparator.json
    try:
        with open(os.path.join(pkg_dir, 'comparator.json'), 'r', encoding='utf-8') as f:
            comp = json.load(f)
            print(f'  Comparator theorems: {comp.get("theorem_names")}')
    except Exception as e:
        print(f'  Comparator error: {e}')

    # Check Challenge.lean imports
    try:
        with open(os.path.join(pkg_dir, 'Challenge.lean'), 'r', encoding='utf-8') as f:
            chal_content = f.read()
            imports = [line.strip() for line in chal_content.split('\n') if line.strip().startswith('import ')]
            print(f'  Challenge imports: {imports}')
            bad = [imp for imp in imports if not imp.startswith('import Mathlib')]
            if bad:
                print(f'  [FAIL] Non-Mathlib imports in Challenge: {bad}')
    except Exception as e:
        print(f'  Challenge error: {e}')

    # Check Solution.lean
    try:
        with open(os.path.join(pkg_dir, 'Solution.lean'), 'r', encoding='utf-8') as f:
            sol_content = f.read()
            has_sorry = 'sorry' in sol_content
            has_axiom = 'axiom ' in sol_content
            print(f'  Solution sorry: {has_sorry}, axiom: {has_axiom}')
    except Exception as e:
        print(f'  Solution error: {e}')

    # Check formalization.yaml
    try:
        with open(os.path.join(pkg_dir, 'formalization.yaml'), 'r', encoding='utf-8') as f:
            yaml_txt = f.read()
            has_v04 = 'version: "v0.4"' in yaml_txt
            has_rel = 'related_formalizations:' in yaml_txt
            has_builds_on = 'relationship: builds-on' in yaml_txt or 'relationship: adapts' in yaml_txt
            has_self_assessed = 'status: self-assessed' in yaml_txt
            print(f'  YAML checks: v0.4={has_v04}, related_formalizations={has_rel}, builds_on={has_builds_on}, self_assessed={has_self_assessed}')
    except Exception as e:
        print(f'  YAML error: {e}')
    print()
