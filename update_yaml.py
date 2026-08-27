import yaml
import os

updates = {
    'palomar/ore_dirac_hamiltonian': {
        "Note on Hamilton circuits": {"year": 1960, "venue": "American Mathematical Monthly"},
        "Some theorems on abstract graphs": {"year": 1952, "venue": "Proceedings of the London Mathematical Society"}
    },
    'palomar/schurs_theorem': {
        "Über die Kongruenz x^m + y^m ≡ z^m (mod p)": {"year": 1916, "venue": "Jahresbericht der Deutschen Mathematiker-Vereinigung"}
    },
    'palomar/dilworth_mirsky': {
        "A Decomposition Theorem for Partially Ordered Sets": {"year": 1950, "venue": "Annals of Mathematics"},
        "A dual of Dilworth's decomposition theorem": {"year": 1971, "venue": "American Mathematical Monthly"}
    },
    'palomar/kneser_lovasz': {
        "Aufgabe 360": {"year": 1955, "venue": "Jahresbericht der Deutschen Mathematiker-Vereinigung"},
        "Kneser's conjecture, chromatic number, and homotopy": {"year": 1978, "venue": "Journal of Combinatorial Theory, Series A"}
    },
    'palomar/frankl_wilson': {
        "Intersection theorems with geometric consequences": {"year": 1981, "venue": "Combinatorica"}
    }
}

for d, patches in updates.items():
    p = os.path.join(d, 'formalization.yaml')
    with open(p, 'r', encoding='utf-8') as f:
        text = f.read()
        
    for title, patch in patches.items():
        if title in text:
            # We will just insert year and venue manually with regex or string replacement
            import re
            pattern = re.compile(r'(\s*-\s*title:\s*"' + re.escape(title) + r'".*?)(\s+relationship:|\s+authors:|\n\s*-|\n\w)', re.DOTALL)
            
            def repl(m):
                # add year and venue before the next field
                return f'{m.group(1)}\n    year: {patch["year"]}\n    venue: "{patch["venue"]}"{m.group(2)}'
            
            text = pattern.sub(repl, text)
            
    with open(p, 'w', encoding='utf-8', newline='\n') as f:
        f.write(text)

print("Updated yaml with year and venue.")
