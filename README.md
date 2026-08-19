# Lean 4 Formalization of Open & Attainable Math Theorems

This repository contains formal Lean 4 statements and sub-lemma roadmaps for **5 open, attainable mathematical theorems/lemmas** ready for autonomous agent proving.

## Formalized Statements

1. **Graham–Pollak Theorem** (`Formalization/GrahamPollak.lean`):
   Decomposition of $K_n$ into complete bipartite graphs requires at least $n - 1$ graphs.
2. **Bollobás's Two Families Theorem** (`Formalization/BollobasTwoFamilies.lean`):
   The foundational set pairs inequality $\sum \binom{|A_i|+|B_i|}{|A_i|}^{-1} \le 1$.
3. **Ore's Theorem on Hamiltonian Graphs** (`Formalization/OreHamiltonian.lean`):
   Sufficient degree-sum condition $\deg(u) + \deg(v) \ge n$ for the existence of Hamiltonian cycles.
4. **Bondy's Theorem on Induced Subsets** (`Formalization/BondyInducedSubsets.lean`):
   Distinguishing $n$ distinct subsets with a coordinate subset of size $\le n - 1$.
5. **Desargues's Theorem (Vector Formulation)** (`Formalization/DesarguesVector.lean`):
   Freek Wiedijk 100 Theorems #53: Perspective from a point implies perspective from a line.

## Getting Started

```bash
lake update
lake exe cache get
lake build
```
