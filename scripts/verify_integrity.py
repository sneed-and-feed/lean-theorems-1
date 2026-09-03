#!/usr/bin/env python3
"""
Integrity and static validation check for Lean 4 formalization packages.
Verifies file encodings, Unix line endings, hermetic imports, and zero proof holes.
"""

import os
import sys
import json
import re

REQUIRED_FILES = ["comparator.json", "formalization.yaml", "Challenge.lean", "Solution.lean"]

def check_file_format(path: str) -> None:
    if not os.path.exists(path):
        sys.exit(f"[FAIL] Missing required file: {path}")
    with open(path, "rb") as f:
        content = f.read()
    if content.startswith(b"\xef\xbb\xbf"):
        sys.exit(f"[FAIL] UTF-8 BOM detected in {path}. Files must be UTF-8 without BOM.")
    if b"\r\n" in content:
        sys.exit(f"[FAIL] CRLF line endings detected in {path}. Files must use Unix LF line endings.")

def main() -> None:
    root_dir = os.path.abspath(".")

    # 1. Check required files exist and have correct encoding / line endings
    for fname in REQUIRED_FILES:
        fpath = os.path.join(root_dir, fname)
        check_file_format(fpath)

    # 2. Validate comparator.json
    comp_path = os.path.join(root_dir, "comparator.json")
    with open(comp_path, "rb") as f:
        first_byte = f.read(1)
        if first_byte != b"{":
            sys.exit(f"[FAIL] comparator.json must start with '{{' (0x7B), got {first_byte!r}")

    with open(comp_path, "r", encoding="utf-8") as f:
        try:
            comp_data = json.load(f)
        except json.JSONDecodeError as e:
            sys.exit(f"[FAIL] Invalid JSON in comparator.json: {e}")

    theorem_names = comp_data.get("theorem_names")
    if not isinstance(theorem_names, list) or len(theorem_names) == 0:
        sys.exit("[FAIL] comparator.json must contain a non-empty 'theorem_names' array.")

    # 3. Hermetic sandbox check: Challenge.lean must only import Mathlib
    chal_path = os.path.join(root_dir, "Challenge.lean")
    with open(chal_path, "r", encoding="utf-8") as f:
        chal_content = f.read()

    for line in chal_content.splitlines():
        s = line.strip()
        if s.startswith("import ") and not (s.startswith("import Mathlib") or s.startswith("import Lean")):
            sys.exit(f"[FAIL] Challenge.lean imports non-library module: {s}")

    # 4. Axiom and proof hole check: Solution.lean must have zero sorry and zero custom axioms
    sol_path = os.path.join(root_dir, "Solution.lean")
    with open(sol_path, "r", encoding="utf-8") as f:
        sol_content = f.read()

    if re.search(r"\bsorry\b", sol_content):
        sys.exit("[FAIL] Solution.lean contains incomplete proofs ('sorry').")

    if re.search(r"^\s*axiom\s+", sol_content, re.MULTILINE):
        sys.exit("[FAIL] Solution.lean introduces custom 'axiom' declarations.")

    # 5. Check declaration presence in Challenge.lean and Solution (including imported Formalization modules)
    imported_texts = []
    for line in sol_content.splitlines():
        line = line.strip()
        if line.startswith("import Formalization."):
            mod_part = line.split("import Formalization.")[1].strip()
            rel_path = os.path.join(root_dir, "Formalization", *mod_part.split(".")) + ".lean"
            if os.path.exists(rel_path):
                with open(rel_path, "r", encoding="utf-8") as f:
                    txt = f.read()
                    if re.search(r"\bsorry\b", txt):
                        sys.exit(f"[FAIL] Imported module {mod_part} contains 'sorry'.")
                    if re.search(r"^\s*axiom\s+", txt, re.MULTILINE):
                        sys.exit(f"[FAIL] Imported module {mod_part} introduces custom 'axiom'.")
                    imported_texts.append(txt)

    combined_sol_search = sol_content + "\n" + "\n".join(imported_texts)

    for thm in theorem_names:
        ident = thm.split(".")[-1]
        pattern = rf"\b(theorem|lemma|def)\s+{re.escape(ident)}\b"
        if not re.search(pattern, chal_content):
            sys.exit(f"[FAIL] Declaration '{thm}' not declared in Challenge.lean.")
        if not re.search(pattern, combined_sol_search):
            sys.exit(f"[FAIL] Declaration '{thm}' not declared in Solution.lean or imported module.")

    print(f"[PASS] Static integrity verified for {len(theorem_names)} target declarations.")

if __name__ == "__main__":
    main()
