import re
import os

path = r'c:\Users\x\Documents\antigravity\lean-theorems-1\formalization.yaml'
with open(path, 'r', encoding='utf-8') as f:
    content = f.read()

disclosure = "To the maintainers' knowledge, the theorem was not found in an exact declaration name, docstring, and type signature search of the pinned Mathlib revision (Mathlib v4.34.0-rc1)."

# Replace the split disclosure with the single line one
content = re.sub(
    r"To the maintainers' knowledge, the theorem was not found in an exact declaration name,\s*docstring, and type signature search of the pinned Mathlib revision \(Mathlib v4.34.0-rc1\).",
    disclosure,
    content
)

with open(path, 'w', encoding='utf-8', newline='\n') as f:
    f.write(content)
