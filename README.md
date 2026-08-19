# Lean 4 Formalization of Open & Attainable Math Theorems

This repository contains formal, fully verified Lean 4 / Mathlib 4 proofs for **5 open, unformalized mathematical theorems/lemmas**, completed autonomously with **0 errors, 0 warnings, 0 axioms, and 0 `sorry`s**.

## Formally Proven Theorems

| # | Theorem | File | Field | Status |
| :-: | :--- | :--- | :--- | :-: |
| 1 | **Desargues's Theorem (Vector Formulation)** | [`Formalization/DesarguesVector.lean`](Formalization/DesarguesVector.lean) | Projective Geometry / Freek #53 | ✅ **100% Proven** |
| 2 | **Graham–Pollak Theorem** | [`Formalization/GrahamPollak.lean`](Formalization/GrahamPollak.lean) | Algebraic Combinatorics | ✅ **100% Proven** |
| 3 | **Bondy's Theorem on Induced Subsets** | [`Formalization/BondyInducedSubsets.lean`](Formalization/BondyInducedSubsets.lean) | Extremal Set Theory / VC Theory | ✅ **100% Proven** |
| 4 | **Bollobás's Two Families Theorem** | [`Formalization/BollobasTwoFamilies.lean`](Formalization/BollobasTwoFamilies.lean) | Extremal Combinatorics | ✅ **100% Proven** |
| 5 | **Ore's & Dirac's Theorems on Hamiltonian Graphs** | [`Formalization/OreHamiltonian.lean`](Formalization/OreHamiltonian.lean) | Structural Graph Theory | ✅ **100% Proven** |

## Verification & Build

To verify the proofs locally using Lean 4 (`v4.34.0-rc1`):

```bash
lake update
lake exe cache get
lake build
```
