# Formalization of Open Combinatorial and Geometric Theorems in Lean 4

This repository provides machine-checked formalizations of five classical theorems in combinatorics, graph theory, extremal set theory, and projective geometry that were previously unformalized in the Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) ecosystem.

All theorems and sub-lemmas are formalized strictly without unproven axioms (`axiom`) or incomplete goals (`sorry`), and are verified against the Lean 4 proof assistant.

---

## Table of Theorems

| # | Theorem | Primary Declaration | Mathematical Domain | Reference |
| :---: | :--- | :--- | :--- | :--- |
| 1 | **Desargues's Theorem (Vector Formulation)** | [`desargues_vector`](Formalization/DesarguesVector.lean) | Projective & Affine Geometry | Desargues (1639), Wiedijk #53 |
| 2 | **Graham–Pollak Theorem** | [`graham_pollak`](Formalization/GrahamPollak.lean) | Algebraic Combinatorics | Graham & Pollak (1971), Tverberg (1982) |
| 3 | **Bondy's Theorem on Induced Subsets** | [`bondy_induced_subsets`](Formalization/BondyInducedSubsets.lean) | Extremal Set Theory & VC Theory | Bondy (1972) |
| 4 | **Bollobás's Two Families Theorem** | [`bollobas_two_families`](Formalization/BollobasTwoFamilies.lean) | Extremal Combinatorics | Bollobás (1965) |
| 5 | **Ore's & Dirac's Theorems** | [`ore_hamiltonian`](Formalization/OreHamiltonian.lean), [`dirac_hamiltonian`](Formalization/OreHamiltonian.lean) | Structural Graph Theory | Ore (1960), Dirac (1952) |

---

## Detailed Theorem Descriptions & Formalization Highlights

### 1. Desargues's Theorem in Vector Form
* **Module:** [`Formalization/DesarguesVector.lean`](Formalization/DesarguesVector.lean)
* **Theorem:** `desargues_vector`
* **Mathematical Statement:** Let $V$ be a module over a commutative ring $K$. If two triangles $(A_1, B_1, C_1)$ and $(A_2, B_2, C_2)$ are in central perspective from a center $O$ with scaling coefficients $(a, b, c)$ and $(\lambda, \mu, \nu)$, then their corresponding side-intersection points:
  $$P = \mu A_2 - \lambda B_2, \quad Q = \nu B_2 - \mu C_2, \quad R = \lambda C_2 - \nu A_2$$
  satisfy the linear dependence relation:
  $$\nu P + \lambda Q + \mu R = 0$$
  and eliminate the center $O$, demonstrating axial perspective (collinearity).
* **Formalization Technique:** Algebraic reduction using module axioms and abelian group normalization (`abel`).

---

### 2. Graham–Pollak Theorem on Bipartite Partitions of Complete Graphs
* **Module:** [`Formalization/GrahamPollak.lean`](Formalization/GrahamPollak.lean)
* **Theorem:** `graham_pollak`
* **Mathematical Statement:** Any partition of the edge set of the complete graph $K_n$ into $m$ complete bipartite subgraphs requires at least $n - 1$ subgraphs ($m \ge n - 1$).
* **Formalization Technique:** 
  1. **Sub-lemma 1 (`sum_sq_identity`):** Expands $(\sum_{i=1}^n x_i)^2 = \sum_{i=1}^n x_i^2 + 2 \sum_{i < j} x_i x_j$.
  2. **Sub-lemma 2 (`bipartite_sum_eq`):** Proves that for any complete bipartite partition $(L_k, R_k)_{k=1}^m$, the cross-term sum satisfies $\sum_{i < j} x_i x_j = \sum_{k=1}^m (\sum_{u \in L_k} x_u)(\sum_{v \in R_k} x_v)$.
  3. **Linear Injectivity & Dimension Theory:** Defines the linear map $T(x) = (\sum x_i, \lambda k. \sum_{u \in L_k} x_u)$. Demonstrates $\ker(T) = \bot$ via the quadratic identity, and applies `LinearMap.finrank_le_finrank_of_injective` to deduce $n \le 1 + m \implies n - 1 \le m$.

---

### 3. Bondy's Theorem on Induced Subsets
* **Module:** [`Formalization/BondyInducedSubsets.lean`](Formalization/BondyInducedSubsets.lean)
* **Theorem:** `bondy_induced_subsets`
* **Mathematical Statement:** Let $\mathcal{F}$ be a family of $n$ distinct subsets of a finite ground set $X$ with $n \ge 1$. There exists a subset $S \subseteq X$ of cardinality $|S| \le n - 1$ such that the restriction map $s \mapsto s \cap S$ is injective on $\mathcal{F}$.
* **Formalization Technique:** Strong induction on $n = |\mathcal{F}|$ (`bondy_aux`) utilizing single-element distinguishing extensions from symmetric differences.

---

### 4. Bollobás's Two Families Theorem (Set Pairs Inequality)
* **Module:** [`Formalization/BollobasTwoFamilies.lean`](Formalization/BollobasTwoFamilies.lean)
* **Theorem:** `bollobas_two_families`
* **Mathematical Statement:** Let $(A_i, B_i)_{i=1}^m$ be pairs of finite sets such that $A_i \cap B_i = \emptyset$ for all $i$, and $A_i \cap B_j \ne \emptyset$ for all $i \ne j$. Then:
  $$\sum_{i=1}^m \frac{1}{\binom{|A_i| + |B_i|}{|A_i|}} \le 1$$
* **Formalization Technique:**
  1. **Disjointness of Linear Ordering Events (`bollobas_events_disjoint`):** Demonstrates that the conditions $\forall a \in A_i, b \in B_i, \pi(a) < \pi(b)$ and $\forall a \in A_j, b \in B_j, \pi(a) < \pi(b)$ are mutually exclusive under any linear ranking $\pi$.
  2. **Combinatorial Probability & Weight Induction (`bollobas_inductive`):** Proves the inequality by strong induction on total set size $\sum_i (|A_i| + |B_i|)$ via uniform element-deletion identities.

---

### 5. Ore's and Dirac's Theorems on Hamiltonian Cycles
* **Module:** [`Formalization/OreHamiltonian.lean`](Formalization/OreHamiltonian.lean)
* **Theorems:** `ore_hamiltonian`, `dirac_hamiltonian`
* **Mathematical Statement:** 
  - **Ore (1960):** A simple graph $G$ on $n \ge 3$ vertices satisfying $\deg(u) + \deg(v) \ge n$ for all distinct non-adjacent vertices $u, v$ contains a Hamiltonian cycle.
  - **Dirac (1952 Corollary):** A simple graph $G$ on $n \ge 3$ vertices with minimum degree $\delta(G) \ge \frac{n}{2}$ contains a Hamiltonian cycle.
* **Formalization Technique:** Longest simple path rerouting via the Pigeonhole Principle on index sets, followed by maximal connected component cycle-expansion.

---

## Repository Structure

```text
.
├── Formalization.lean                    # Root library module importing all formalized theorems
├── Formalization/
│   ├── DesarguesVector.lean              # Desargues's Theorem (Vector Formulation)
│   ├── GrahamPollak.lean                 # Graham–Pollak Theorem & Bipartite Partition Identities
│   ├── BondyInducedSubsets.lean          # Bondy's Theorem on Induced Subsets
│   ├── BollobasTwoFamilies.lean          # Bollobás's Two Families Theorem (Set Pairs Inequality)
│   └── OreHamiltonian.lean               # Ore's & Dirac's Theorems on Hamiltonian Graphs
├── lakefile.toml                         # Lake build system manifest
├── lean-toolchain                        # Pinned Lean 4 toolchain (leanprover/lean4:v4.34.0-rc1)
└── README.md
```

---

## Build and Verification

### Prerequisites
- [Elan](https://github.com/leanprover/elan) (Lean Version Manager)

### Compiling and Verifying
To fetch dependencies, download precompiled Mathlib oleans, and verify all proofs:

```bash
lake update
lake exe cache get
lake build
```

Individual modules can be compiled independently:

```bash
lake build Formalization.GrahamPollak
lake build Formalization.BollobasTwoFamilies
lake build Formalization.BondyInducedSubsets
lake build Formalization.OreHamiltonian
lake build Formalization.DesarguesVector
```

---

## References

1. **Bollobás, B.** (1965). *On generalized graphs*. Acta Mathematica Academiae Scientiarum Hungarica, 16(3-4), 447–452.
2. **Bondy, J. A.** (1972). *Induced subsets and colour-critical graphs*. Congressus Numerantium, 5, 71–77.
3. **Dirac, G. A.** (1952). *Some theorems on abstract graphs*. Proceedings of the London Mathematical Society, 3(1), 69–81.
4. **Graham, R. L., & Pollak, H. O.** (1971). *On the addressing problem for loop switching*. Bell System Technical Journal, 50(8), 2495–2519.
5. **Ore, O.** (1960). *Note on Hamilton circuits*. The American Mathematical Monthly, 67(1), 55.
6. **Tverberg, H.** (1982). *On the decomposition of $K_n$ into complete bipartite graphs*. Journal of Graph Theory, 6(4), 493–494.
7. **Wiedijk, F.** (2008). *Formalizing 100 Theorems*. http://www.cs.ru.nl/~freek/100/
