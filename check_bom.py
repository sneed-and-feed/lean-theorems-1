import os

base_dir = r'c:\Users\x\Documents\antigravity\lean-theorems-1\palomar'
packages = ['picks_theorem', 'art_gallery_theorem', 'erdos_szekeres_convex', 'crossing_lemma', 'de_bruijn_erdos']

print("Checking...")
for pkg in packages:
    pkg_dir = os.path.join(base_dir, pkg)
    if not os.path.exists(pkg_dir):
        print(f"Dir not found: {pkg_dir}")
        continue
    for root, dirs, files in os.walk(pkg_dir):
        for f in files:
            path = os.path.join(root, f)
            with open(path, 'rb') as file:
                content = file.read()
                
            issues = []
            if content.startswith(b'\xef\xbb\xbf'):
                issues.append('BOM found')
                content = content[3:]
                
            if b'\r\n' in content:
                issues.append('CRLF found')
                content = content.replace(b'\r\n', b'\n')
                
            if issues:
                with open(path, 'wb') as file:
                    file.write(content)
                print(f'Fixed {issues} in {path}')
print('Done.')
