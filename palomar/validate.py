import os

base_dir = r'c:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = ['sylvester_gallai', 'hall_marriage', 'sperners_lemma', 'descartes_rule_of_signs', 'radon_helly', 'picks_theorem']

for pkg in packages:
    pkg_dir = os.path.join(base_dir, pkg)
    comp_path = os.path.join(pkg_dir, 'comparator.json')
    challenge_path = os.path.join(pkg_dir, 'Challenge.lean')
    solution_path = os.path.join(pkg_dir, 'Solution.lean')
    yaml_path = os.path.join(pkg_dir, 'formalization.yaml')
    
    try:
        with open(comp_path, 'rb') as f:
            content = f.read()
            c1_bom = 'Pass' if content[0] == 0x7B else 'Fail'
            c1_lf = 'Fail (CRLF)' if b'\r\n' in content else 'Pass'
    except Exception as e:
        c1_bom = str(e)
        c1_lf = ''
        
    try:
        with open(challenge_path, 'r', encoding='utf-8') as f:
            chal_content = f.read()
            imports = [line for line in chal_content.split('\n') if line.startswith('import ')]
    except Exception as e:
        imports = str(e)
        
    try:
        with open(solution_path, 'r', encoding='utf-8') as f:
            sol_content = f.read()
            has_sorry = 'sorry' in sol_content
            has_axiom = 'axiom ' in sol_content
    except Exception as e:
        has_sorry = str(e)
        has_axiom = False
        
    print(f'--- {pkg} ---')
    print(f'Check 1 (BOM): {c1_bom}, Check 1 (LF): {c1_lf}')
    print(f'Imports: {imports}')
    print(f'Solution sorry: {has_sorry}, axiom: {has_axiom}')
