# Lean 4 Project Rules: lean-unformalized-theorems

## Mandatory Mathlib Prerequisite & Feasibility Research Protocol

> [!IMPORTANT]
> **Before attempting to formalize a non-trivial theorem or proof strategy, agents MUST conduct a pre-formalization feasibility research step.**
> Language models frequently attempt purely combinatorial inductions or elementary workarounds for deep theorems that mathematically require unformalized prerequisites (e.g., topological degree theory, colorful Carathéodory, algebraic topology, spectral graph theory, homology). This leads to infinite "spiral" loops.

### Feasibility Research Checklist:
1. **Mathematical Strategy Identification:**
   - Identify the exact mathematical machinery required for the proof (e.g., hyperplane separation, Helly's theorem, Carathéodory, homology, linear algebra over finite fields).
2. **Mathlib Inventory Verification:**
   - Use `lean_loogle`, `lean_leansearch`, `lean_local_search`, and `search_web` to verify whether the required lemmas, structures, and definitions actually exist in the current Mathlib version.
3. **Avoid Purely Elementary Fallbacks for Deep Results:**
   - If a theorem requires a topological or geometric prerequisite that does NOT exist in Mathlib, **DO NOT** attempt to invent ad-hoc combinatorial workarounds or infinite induction chains.
   - Instead, either:
     (a) Explicitly isolate the missing prerequisite as a clearly stated lemma/axiom/stub for future formalization, or
     (b) Pivot to an alternative proof formulation whose prerequisites ARE available in Mathlib.

## Lean 4 Build & Tooling Protocol

- `lake build` and `lake build Formalization.<Module>` commands in PowerShell / terminal (`run_command`) **ARE FULLY PERMITTED** for checking compilation, validating theorem integrity, and running builds.
- Agents may also use `call_mcp_tool` with `ServerName: "lean-lsp"` (when available) as an optional alternative for quick goal inspection.
