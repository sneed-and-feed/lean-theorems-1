# Formalization of Open Combinatorial and Geometric Theorems in Lean 4

This repository provides machine-checked formalizations of classical theorems in combinatorics, graph theory, algebra, extremal set theory, and projective geometry that were previously unformalized in the Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) ecosystem.

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
| 6 | **Descartes's Rule of Signs** | [`descartes_rule_of_signs`](Formalization/DescartesSigns.lean) | Real Algebraic Geometry & Polynomials | Descartes (1637), Wiedijk #73 |
| 7 | **Euler's Polyhedron Formula** | [`euler_polyhedron_formula`](Formalization/EulerPolyhedron.lean), [`euler_connected_graph`](Formalization/EulerPolyhedron.lean) | Topological Graph Theory & Topology | Euler (1758), Cauchy (1813), Wiedijk #13 |
| 8 | **Sperner's Lemma (1D & 2D)** | [`sperner_1d_parity`](Formalization/SpernersLemma.lean), [`sperner_2d_parity`](Formalization/SpernersLemma.lean), [`sperner_2d_exists`](Formalization/SpernersLemma.lean) | Topological Combinatorics & Fixed Point Theory | Sperner (1928), Wiedijk #57 |
| 9 | **De Bruijn–Erdős Theorem on Incidence Geometry** | [`de_bruijn_erdos`](Formalization/DeBruijnErdos.lean) | Incidence Geometry & Extremal Combinatorics | De Bruijn & Erdős (1948) |
| 10 | **Schur's Theorem on Sum-Free Partitions** | [`schurs_theorem`](Formalization/SchursTheorem.lean), [`ramsey_triangle`](Formalization/SchursTheorem.lean) | Ramsey Theory & Additive Combinatorics | Schur (1916) |
| 11 | **Erdős–Ko–Rado Theorem on Intersecting Families** | [`erdos_ko_rado`](Formalization/ErdosKoRado.lean), [`erdos_ko_rado_disjoint_pair`](Formalization/ErdosKoRado.lean), [`erdos_ko_rado_powersetCard`](Formalization/ErdosKoRado.lean) | Extremal Set Theory & Combinatorics | Erdős, Ko, & Rado (1961), Katona (1972) |
| 12 | **Sylvester–Gallai Theorem** | [`sylvester_gallai`](Formalization/SylvesterGallai.lean) | Incidence & Euclidean Geometry | Sylvester (1893), Gallai (1944), Kelly (1948), Wiedijk #98 |
| 13 | **Hall's Marriage Theorem** | [`hall_marriage_theorem`](Formalization/HallMarriage.lean) | Combinatorial Matching Theory | Hall (1935), Halmos & Vaughan (1950), Wiedijk #87 |
| 14 | **The Friendship Theorem** | [`friendship_theorem`](Formalization/FriendshipTheorem.lean) | Extremal & Spectral Graph Theory | Erdős, Rényi, & Sós (1966), Wilf (1971) |
| 15 | **Radon's Lemma & Helly's Theorem** | [`radons_theorem`](Formalization/RadonHelly.lean), [`hellys_theorem`](Formalization/RadonHelly.lean) | Convex & Discrete Geometry | Radon (1921), Helly (1923), Wiedijk #99 |
| 16 | **Tverberg's Theorem** *(In Progress)* | [`tverbergs_theorem`](Formalization/TverbergsTheorem.lean) | Convex & Discrete Geometry | Tverberg (1966) |
| 17 | **Dilworth's Decomposition Theorem** *(In Progress)* | [`dilworth_theorem`](Formalization/DilworthTheorem.lean), [`dilworth_duality`](Formalization/DilworthTheorem.lean) | Poset & Combinatorial Order Theory | Dilworth (1950), Perles (1963) |
| 18 | **Chvátal's Art Gallery Theorem** *(In Progress)* | [`art_gallery_theorem`](Formalization/ArtGalleryTheorem.lean) | Computational Geometry & Graph Coloring | Chvátal (1975), Fisk (1978) |
| 19 | **Cauchy's Arm Lemma & Convex Rigidity** *(In Progress)* | [`cauchy_arm_lemma`](Formalization/CauchyArmLemma.lean) | Discrete & Euclidean Geometry | Cauchy (1813) |

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
* **Mathematical Statement:** Any partition of the edge set of the complete graph $K_n$ into $m$ complete bipartite graphs $K_{A_k, B_k}$ requires at least $n - 1$ bipartite graphs:
  $$m \ge n - 1$$
* **Formalization Technique:** Tverberg's algebraic method, formalizing the bilinear form identity $\sum_{i < j} x_i x_j = \sum_{k=1}^m (\sum_{u \in A_k} x_u)(\sum_{v \in B_k} x_v)$ and establishing that $\sum_{i=1}^n x_i^2 = 0$ under orthogonal linear constraints.

---

### 3. Bondy's Theorem on Induced Subsets
* **Module:** [`Formalization/BondyInducedSubsets.lean`](Formalization/BondyInducedSubsets.lean)
* **Theorem:** `bondy_induced_subsets`
* **Mathematical Statement:** Let $\mathcal{A}$ be a family of $n$ distinct subsets of an $n$-element universe $U$. There exists a subset $S \subseteq U$ with $|S| \le n - 1$ such that the projections $\{A \cap S \mid A \in \mathcal{A}\}$ are all distinct.
* **Formalization Technique:** Extremal induction and greedy vertex elimination maintaining family separation.

---

### 4. Bollobás's Two Families Theorem (Set Pairs Inequality)
* **Module:** [`Formalization/BollobasTwoFamilies.lean`](Formalization/BollobasTwoFamilies.lean)
* **Theorem:** `bollobas_two_families`
* **Mathematical Statement:** Let $A_1, \dots, A_m$ and $B_1, \dots, B_m$ be finite sets such that $A_i \cap B_j = \emptyset \iff i = j$. Then:
  $$\sum_{i=1}^m \frac{1}{\binom{|A_i| + |B_i|}{|A_i|}} \le 1$$
* **Formalization Technique:** Uniform random permutation averaging and probability measure bounding over symmetric groups.

---

### 5. Ore's and Dirac's Theorems on Hamiltonian Cycles
* **Module:** [`Formalization/OreHamiltonian.lean`](Formalization/OreHamiltonian.lean)
* **Theorems:** `ore_hamiltonian`, `dirac_hamiltonian`
* **Mathematical Statement:**
  - **Ore (1960):** If a simple graph $G$ on $n \ge 3$ vertices satisfies $\deg(u) + \deg(v) \ge n$ for every pair of non-adjacent vertices $u \ne v$, then $G$ is Hamiltonian.
  - **Dirac (1952):** If $\deg(v) \ge n/2$ for all vertices, then $G$ is Hamiltonian.
* **Formalization Technique:** Maximum path augmentation and cycle closure via common predecessor pigeonholing.

---

### 6. Descartes's Rule of Signs (Freek Wiedijk #73)
* **Module:** [`Formalization/DescartesSigns.lean`](Formalization/DescartesSigns.lean)
* **Theorem:** `descartes_rule_of_signs`
* **Mathematical Statement:** The number of positive real roots $Z(P)$ of a non-zero real polynomial $P(X)$ does not exceed the number of sign variations $V(P)$ in its sequence of non-zero coefficients, and $V(P) - Z(P)$ is an even integer:
  $$Z(P) \le V(P) \quad \text{and} \quad V(P) \equiv Z(P) \pmod 2$$
* **Formalization Technique:** Induction on root factors $(X - r)$ with $r > 0$ and Sign Variations Parity Invariants.

---

### 7. Euler's Polyhedron Formula (Freek Wiedijk #13)
* **Module:** [`Formalization/EulerPolyhedron.lean`](Formalization/EulerPolyhedron.lean)
* **Theorems:** `euler_polyhedron_formula`, `euler_connected_graph`
* **Mathematical Statement:** For any connected planar graph (or convex polyhedron boundary) with $V$ vertices, $E$ edges, and $F$ faces:
  $$V - E + F = 2$$
* **Formalization Technique:** Induction on independent cycles ($E - V + 1$) via tree contraction and boundary dual edge deletion.

---

### 8. Sperner's Lemma in 1D and 2D (Freek Wiedijk #57)
* **Module:** [`Formalization/SpernersLemma.lean`](Formalization/SpernersLemma.lean)
* **Theorems:** `sperner_1d_parity`, `sperner_1d_exists`, `sperner_2d_parity`, `sperner_2d_odd`, `sperner_2d_exists`
* **Mathematical Statement:**
  - **1D Sperner:** For any coloring $f : \{0, \dots, n\} \to \{0, 1\}$, the number of color-switching steps has the same parity as $[f(0) \ne f(n)]$.
  - **2D Sperner:** For any 2D triangulation $T$ (simplicial surface with boundary) with vertex coloring $c : V \to \{0, 1, 2\}$, the number of panchromatic triangles and boundary $0$-$1$ edges share the same parity modulo 2:
    $$|\{t \in T \mid c(t) = \{0, 1, 2\}\}| \equiv |E_{\text{bd}}^{01}| \pmod 2$$
* **Formalization Technique:** Double-counting the sum of local door counts $\sum_{t \in T} \operatorname{doorCount}(t) = |E_{\text{bd}}^{01}| + 2 |E_{\text{int}}^{01}|$ and machine-checking the local 27-case parity invariant.

---

### 9. De Bruijn–Erdős Theorem on Incidence Geometry
* **Module:** [`Formalization/DeBruijnErdos.lean`](Formalization/DeBruijnErdos.lean)
* **Theorems:** `de_bruijn_erdos`, `de_bruijn_erdos'`
* **Mathematical Statement:** Let $\mathcal{P}$ be a finite set of $n \ge 3$ points and $\mathcal{L}$ a collection of subsets of $\mathcal{P}$ called lines such that every line contains at least 2 points, every pair of distinct points lies on a unique line, and not all points are collinear. Then the number of lines is at least the number of points:
  $$|\mathcal{L}| \ge |\mathcal{P}|$$
* **Formalization Technique:**
  1. **Non-incident Point-Line Lower Bound (`card_line_le_pointDegree`):** Proves that for $p \notin L$, mapping $q \in L$ to the unique line through $p$ and $q$ is injective, so $|L| \le \deg(p)$.
  2. **Non-incident Line Existence (`exists_line_not_mem`, `two_le_pointDegree`):** Shows $\deg(p) \ge 2 > 0$ for all $p \in \mathcal{P}$.
  3. **Fubini Double Summation (`double_sum_swap`):** Swaps double sums over non-incident pairs $E = \{(p, L) \mid p \notin L\}$.
  4. **Strict Pointwise Fraction Inequality (`frac_sub_lt_frac`, `sum_frac_lt_card_lines`):** Proves $\sum_{p \in \mathcal{P}} \frac{|\mathcal{L}| - \deg(p)}{|\mathcal{P}| - \deg(p)} < |\mathcal{L}|$ if $|\mathcal{L}| < |\mathcal{P}|$, deriving a direct contradiction.

---

### 10. Schur's Theorem on Sum-Free Partitions
* **Module:** [`Formalization/SchursTheorem.lean`](Formalization/SchursTheorem.lean)
* **Theorems:** `schurs_theorem`, `ramsey_triangle`, `schurs_partition_theorem`
* **Mathematical Statement:**
  - **Schur's Theorem (1916):** For any integer $r \ge 1$, there exists an integer $N = R_r(3) = \text{ramseyTriangleBound}(r)$ such that for every $r$-coloring $\chi : \{1, \dots, N\} \to \{1, \dots, r\}$, there exists a monochromatic solution to:
    $$x + y = z$$
  - **Multicolor Triangle Ramsey Theorem:** Every complete graph with at least $\text{ramseyTriangleBound}(r)$ vertices whose edges are colored with $r$ colors contains a monochromatic triangle.
* **Formalization Technique:**
  1. **Ramsey Recurrence:** Formalizes $R(0) = 2, R(r+1) = (r+1)R(r) + 1$ (`ramseyTriangleBound`).
  2. **Multicolor Ramsey Induction (`ramsey_triangle`):** Inducts on $r$ using the Pigeonhole Principle across star edge-colorings (`exists_fiber_ge`) and color contraction (`reduceColor_inj`).
  3. **Difference Coloring Reduction:** Defines edge coloring $c(u, v) = \chi(|u - v|)$ on vertices $\{0, 1, \dots, N\}$. Monochromatic triangle $a < b < c$ yields $x = b - a, y = c - b, z = c - a$ with $x + y = z$ and $\chi(x) = \chi(y) = \chi(z)$.

---

### 11. Erdős–Ko–Rado Theorem on Intersecting Families
* **Module:** [`Formalization/ErdosKoRado.lean`](Formalization/ErdosKoRado.lean)
* **Theorems:** `erdos_ko_rado`, `erdos_ko_rado_disjoint_pair`, `erdos_ko_rado_powersetCard`, `katona_arc_lemma`
* **Mathematical Statement:**
  Let $n \ge 2k$ with $k \ge 1$, and let $\mathcal{F}$ be an intersecting family of $k$-element subsets of an $n$-element universe $\alpha$ (i.e. $\forall A, B \in \mathcal{F}, \neg \text{Disjoint } A \, B$). Then:
  $$|\mathcal{F}| \le \binom{n-1}{k-1}$$
  Equivalently, if $|\mathcal{F}| > \binom{n-1}{k-1}$, then $\mathcal{F}$ contains at least two disjoint sets.
* **Formalization Technique:**
  1. **Katona's Circle Method (`cyclicArc`, `katona_arc_lemma`):** Embeds elements on the cyclic group $\mathbb{Z}/n\mathbb{Z}$. A cyclic arc of length $k$ starting at $i$ is $A_i = \{i, i+1, \dots, i+k-1\}$. For $2k \le n$, pairs of arcs $(A_r, A_{r-k})$ are disjoint, partitioning non-zero intersecting shifts into disjoint pairs. Hence any pairwise intersecting collection of cyclic arcs has size at most $k$.
  2. **Shift Invariance & Fiber Cardinality (`arcOf`, `card_fiber_arcOf`):** Connects bijections $e : \alpha \simeq \mathbb{Z}/n\mathbb{Z}$ with Mathlib's `Numbering α` (`KatonaCircle`). For every fixed $k$-set $A \in \mathcal{F}$ and every shift index $i \in \mathbb{Z}/n\mathbb{Z}$, the fiber of bijections mapping $A$ to the arc at $i$ has exact cardinality $k! (n-k)!$.
  3. **Double Counting Summation (`erdos_ko_rado`):** Double-counts the incidence sum $\sum_{e \in \alpha \simeq \mathbb{Z}/n\mathbb{Z}} \sum_{i \in \mathbb{Z}/n\mathbb{Z}} \mathbf{1}_{\{e^{-1}(\text{arc}(i)) \in \mathcal{F}\}}$, upper-bounding by $k \cdot n!$ via Katona's arc lemma and evaluating to $n |\mathcal{F}| k! (n-k)!$.
  4. **Exact Factorial Cancellation (`choose_bound_of_double_counting`):** Cancels $n k$ to obtain $|\mathcal{F}| (k-1)! (n-k)! \le (n-1)!$, and applies `Nat.choose_mul_factorial_mul_factorial` to deduce $|\mathcal{F}| \le \binom{n-1}{k-1}$.

---

### 12. Sylvester–Gallai Theorem on Ordinary Lines (Freek Wiedijk #98)
* **Module:** [`Formalization/SylvesterGallai.lean`](Formalization/SylvesterGallai.lean)
* **Theorem:** `sylvester_gallai`
* **Mathematical Statement:** Let $S \subset \mathbb{R}^2$ be a finite set of points in the Euclidean plane. If not all points of $S$ lie on a single straight line ($\neg \text{SetCollinear } S$), then there exists an **ordinary line**—a straight line passing through *exactly two* points of $S$:
  $$\exists p \in S, \, \exists q \in S, \, p \ne q \wedge \text{IsOrdinaryLine } S \, p \, q$$
* **Formalization Highlights & Proof Technique:**
  1. **Self-Contained 2D Cartesian Geometry (`cross`, `dot`, `sqNorm`, `signedArea`):** Formalizes planar coordinates without metric space overhead. Proves signed area antisymmetry, cyclic invariance, and equivalence with collinearity.
  2. **Candidate Point-Line Triples & Global Minimization (`candidateTriples`, `distSq`):** Filters $S \times S \times S$ to candidate triples $(p, a, b)$ with $a \ne b$ and $p \notin \text{line}(a, b)$. Uses `Finset.exists_min_image` on the squared distance metric $\text{distSq}(p, a, b) = \frac{(\text{signedArea}(a, b, p))^2}{\|b - a\|^2}$ to extract a minimal triple $(p_0, a_0, b_0)$.
  3. **1D Parametrization & Projection (`collinear_iff_param`, `pythagorean_decomp`):** Parametrizes any point on $\text{line}(a_0, b_0)$ as $r(t) = a_0 + t(b_0 - a_0)$ via dot products. Establishes the Pythagorean distance decomposition from $a = r(t_a)$ to $p_0$ via the orthogonal projection $q_0 = r(t_q)$.
  4. **Kelly's Closer-Pair Ordering Contradiction (`exists_closer_pair_1d`):** Proves that among three distinct points $a_0, b_0, c$ on $L_0$ and the projection parameter $t_q$, there exists a pair of parameters $t_i, t_j$ satisfying $(t_j - t_i)^2 \le (t_i - t_q)^2$. Shows that the new pair $(b = r(t_j), \text{line}(p_0, a = r(t_i)))$ has strictly smaller squared distance than $(p_0, a_0, b_0)$, establishing by contradiction that $L_0$ contains exactly 2 points of $S$.

---

### 13. Hall's Marriage Theorem (Freek Wiedijk #87)
* **Module:** [`Formalization/HallMarriage.lean`](Formalization/HallMarriage.lean)
* **Theorem:** `hall_marriage_theorem`, `hall_marriage_necessary`
* **Mathematical Statement:** Let $A_1, \dots, A_n$ be a finite collection of finite sets indexed by a finite type $\iota$. A **System of Distinct Representatives (SDR)** (or transversal) is an injective choice function $f : \iota \to \alpha$ with $\forall i \in \iota, f(i) \in A_i$.
  An SDR exists if and only if **Hall's Marriage Condition** holds: for every subset of indices $J \subseteq \iota$,
  $$\left| \bigcup_{i \in J} A_i \right| \ge |J|$$
* **Formalization Highlights & Proof Technique:**
  1. **Halmos & Vaughan Strong Induction (`hall_marriage_finset`):** Formulates and machine-proves the existence of partial SDRs for arbitrary subfamilies $S \subseteq \iota$ over any indexed family $A : \iota \to \text{Finset } \alpha$ by strong induction on $n = |S|$.
  2. **Tight Subfamily Reduction (Case 1):** If there exists a non-empty proper tight subset $J_0 \subset S$ ($0 < |J_0| < |S|$) with $|\bigcup_{i \in J_0} A_i| = |J_0|$, extracts an SDR $f_1$ on $J_0$ with image $T = \bigcup_{i \in J_0} A_i$. On $K = S \setminus J_0$, defines the reduced family $A'_i = A_i \setminus T$, proves that $A'$ preserves Hall's condition on $K$ via `union_biUnion` and `union_sdiff_self_right`, obtains $f_2$ on $K$ disjoint from $T$, and stitches $f_1$ and $f_2$.
  3. **Non-Tight Case Reduction (Case 2):** If no proper non-empty tight subset exists, every non-empty $J \subset S$ strictly satisfies $|\bigcup_{i \in J} A_i| \ge |J| + 1$. Isolates an index $i_0 \in S$ and an element $x \in A_{i_0}$, reduces to $K = S \setminus \{i_0\}$ with trimmed sets $A'_i = A_i \setminus \{x\}$, proves Hall's condition on $K$ via `card_sdiff_singleton_ge`, obtains $f_0$ on $K$, and sets $f(i_0) = x$.
  4. **Global Equivalence on `Finset.univ`:** Instantiates the finset induction on $S = \text{Finset.univ}$ to deduce the full bidirectional equivalence `(∃ f : ι → α, IsSDR A f) ↔ HallCondition A`, handling both empty and inhabited index types $\iota$.

---

### 14. The Friendship Theorem (Erdős–Rényi–Sós 1966)
* **Module:** [`Formalization/FriendshipTheorem.lean`](Formalization/FriendshipTheorem.lean)
* **Theorem:** `friendship_theorem`
* **Mathematical Statement:** In any finite party (simple graph $G = (V, E)$ on $|V| \ge 3$) where every pair of distinct individuals shares *exactly one* common friend, there exists a politician (a universal vertex $w \in V$) who is friends with everyone:
  $$\forall u \ne v, |N(u) \cap N(v)| = 1 \implies \exists w \in V, \forall v \ne w, G.\text{Adj } w \, v$$
* **Formalization Highlights & Proof Technique:**
  1. **Equidegree for Non-Adjacent Vertices (`degree_eq_of_not_adj`):** Formalizes the canonical bijection between $N(u) \setminus \{w\}$ and $N(v) \setminus \{w\}$ given by unique common neighbors, proving $\deg(u) = \deg(v)$ whenever $u \not\sim v$.
  2. **Non-Regular Universal Vertex Classification (`exists_universal_of_exists_degree_ne`):** If degrees are not all equal, proves that adjacent vertices of differing degrees contain a universal vertex with degree $|V| - 1$.
  3. **Regular Graph Invariant & Cardinality (`card_V_eq_k_mul_k_sub_one_add_one`):** If $G$ is $k$-regular, double-counts common neighbor pairs to prove $|V| = k(k - 1) + 1$. Pairs vertices via involution without fixed points (`even_card_of_involution`) to establish that $k$ must be even.
  4. **Closed Walk Cyclic Group Action (`no_regular_friendship_graph_ge_three`):** Takes a prime $p \mid (k - 1)$ (where $p \ge 3$ because $k$ is even and $k \ge 4$). Defines the group action of $\text{Multiplicative}(\mathbb{Z}/p\mathbb{Z})$ on closed walks of length $p$. Proves that the action has 0 fixed points since $G$ has no self-loops (`closedWalk_fixedPoints_empty`), hence $|ClosedWalk| \equiv 0 \pmod p$ via `IsPGroup.card_modEq_card_fixedPoints`.
  5. **Trace Equivalence Contradiction:** Expresses closed walks via vertex walk vectors (`WalkVec`, `cwAtEquivWalkVec`). By walk induction modulo $p$, $(A^p)_{v,v} \equiv 1 \pmod p$, so $|ClosedWalk| = \sum_{v \in V} (A^p)_{v,v} \equiv |V| = k(k-1)+1 \equiv 1 \pmod p$. The resulting congruence $0 \equiv 1 \pmod p$ implies $p \mid 1$, eliminating all $k \ge 3$.
  6. **Base Case $k = 2$:** Reduces 2-regular friendship graphs directly to the triangle $K_3$ (`two_regular_has_universal`), in which every vertex is universal.

---

### 15. Radon's Lemma and Helly's Theorem (Freek Wiedijk #99)
* **Module:** [`Formalization/RadonHelly.lean`](Formalization/RadonHelly.lean)
* **Theorems:** `radons_theorem`, `hellys_theorem`
* **Mathematical Statement:**
  - **Radon's Lemma (1921):** Any set $S \subset \mathbb{R}^d$ of $d + 2$ points can be partitioned into two disjoint subsets $A, B \subseteq S$ whose convex hulls intersect:
    $$A \cap B = \emptyset, \quad A \cup B = S, \quad \operatorname{conv}(A) \cap \operatorname{conv}(B) \ne \emptyset$$
  - **Helly's Theorem (1923):** Let $C_1, \dots, C_n$ be a finite collection of convex subsets in $\mathbb{R}^d$. If every subcollection of at most $d + 1$ sets has a non-empty intersection, then the entire collection has a non-empty intersection:
    $$\bigcap_{i=1}^n C_i \ne \emptyset$$
* **Formalization Highlights & First-Principles Proof Technique:**
  1. **Linear Dependence via Nullity (`radonMap`, `exists_nonzero_radon_coeff`):** Maps $c \in (\text{Fin } (d + 2) \to \mathbb{R})$ to $(\sum_i c_i, \sum_i c_i v_i) \in \mathbb{R} \times (\text{Fin } d \to \mathbb{R})$. Since $\dim(\text{domain}) = d + 2 > d + 1 = \dim(\text{codomain})$, dimension comparison proves non-injectivity and extracts a non-zero kernel vector $c \ne 0$ satisfying $\sum_i c_i = 0$ and $\sum_i c_i v_i = 0$.
  2. **Sign Splitting & Barycentric Combination:** Partitions indices into $I_+ = \{i \mid c_i > 0\}$ and $I_- = \{i \mid c_i \le 0\}$, proving both are non-empty and disjoint. Constructs the barycentric intersection point $p = \sum_{i \in I_+} \frac{c_i}{C} v_i = \sum_{j \in I_-} \frac{-c_j}{C} v_j$ with $C = \sum_{I_+} c_i > 0$, and machine-checks that $p \in \operatorname{conv}(A) \cap \operatorname{conv}(B)$ using `Finset.centerMass`.
  3. **Helly Strong Induction on Finite Subfamilies (`hellys_theorem_card`):** Formulates induction on the cardinality $n = |S|$ of subfamilies $S \subseteq \iota$. Handles the base case $n \le d + 1$ directly. For the base step $n = d + 2$, constructs points $p_j \in \bigcap_{i \in S \setminus \{j\}} C_i$; either finds duplicate points or applies `radons_theorem` on the distinct points to deduce $p \in \bigcap_{i \in S} C_i$. For $n > d + 2$, contracts the family by merging $C_a$ and $C_b$ into $C_a \cap C_b$ on $S \setminus \{b\}$.
  4. **Full Global Intersection:** Concludes $\bigcap_{i \in \iota} C_i \ne \emptyset$ by instantiating the family induction on $S = \text{Finset.univ}$.

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
│   ├── OreHamiltonian.lean               # Ore's & Dirac's Theorems on Hamiltonian Graphs
│   ├── DescartesSigns.lean               # Descartes's Rule of Signs (Freek Wiedijk #73)
│   ├── EulerPolyhedron.lean              # Euler's Polyhedron Formula (Freek Wiedijk #13)
│   ├── SpernersLemma.lean                # Sperner's Lemma (1D & 2D) (Freek Wiedijk #57)
│   ├── DeBruijnErdos.lean                # De Bruijn–Erdős Theorem on Incidence Geometry
│   ├── SchursTheorem.lean                # Schur's Theorem on Sum-Free Partitions & Ramsey Triangles
│   ├── ErdosKoRado.lean                  # Erdős–Ko–Rado Theorem & Katona's Circle Method
│   ├── SylvesterGallai.lean              # Sylvester–Gallai Theorem (Freek Wiedijk #98)
│   ├── HallMarriage.lean                 # Hall's Marriage Theorem (Freek Wiedijk #87)
│   ├── FriendshipTheorem.lean            # The Friendship Theorem (Erdős–Rényi–Sós 1966)
│   ├── RadonHelly.lean                   # Radon's Lemma & Helly's Theorem (Freek Wiedijk #99)
│   ├── TverbergsTheorem.lean             # Tverberg's Theorem on Intersecting Convex Hulls [Stub]
│   ├── DilworthTheorem.lean              # Dilworth's Decomposition Theorem for Posets [Stub]
│   ├── ArtGalleryTheorem.lean            # Chvátal's Art Gallery Theorem & Fisk's 3-Coloring [Stub]
│   └── CauchyArmLemma.lean               # Cauchy's Arm Lemma and Convex Rigidity [Stub]
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
lake build Formalization.DescartesSigns
lake build Formalization.EulerPolyhedron
lake build Formalization.SpernersLemma
lake build Formalization.DeBruijnErdos
lake build Formalization.SchursTheorem
lake build Formalization.ErdosKoRado
lake build Formalization.SylvesterGallai
lake build Formalization.HallMarriage
lake build Formalization.FriendshipTheorem
lake build Formalization.RadonHelly
lake build Formalization.TverbergsTheorem
lake build Formalization.DilworthTheorem
lake build Formalization.ArtGalleryTheorem
lake build Formalization.CauchyArmLemma
```

---

## References

1. **Aigner, M., & Ziegler, G. M.** (2018). *Proofs from THE BOOK*. Springer, Berlin, Heidelberg.
2. **Bollobás, B.** (1965). *On generalized graphs*. Acta Mathematica Academiae Scientiarum Hungarica, 16(3-4), 447–452.
3. **Bondy, J. A.** (1972). *Induced subsets and colour-critical graphs*. Congressus Numerantium, 5, 71–77.
4. **Cauchy, A. L.** (1813). *Recherches sur les polyèdres: Premier Mémoire*. Journal de l'École Polytechnique, 9, 68–86.
5. **Chvátal, V.** (1975). *A combinatorial theorem in plane geometry*. Journal of Combinatorial Theory, Series B, 18(1), 39–41.
6. **de Bruijn, N. G., & Erdős, P.** (1948). *On a combinatorial problem*. Indagationes Mathematicae, 10, 421–423.
7. **Descartes, R.** (1637). *La Géométrie*. Discours de la méthode, Leyden.
8. **Dilworth, R. P.** (1950). *A decomposition theorem for partially ordered sets*. Annals of Mathematics, 51(1), 161–166.
9. **Dirac, G. A.** (1952). *Some theorems on abstract graphs*. Proceedings of the London Mathematical Society, 3(1), 69–81.
10. **Erdős, P., Ko, C., & Rado, R.** (1961). *Intersection theorems for systems of finite sets*. The Quarterly Journal of Mathematics, 12(1), 313–320.
11. **Erdős, P., Rényi, A., & Sós, V. T.** (1966). *On a problem of graph theory*. Studia Scientiarum Mathematicarum Hungarica, 1, 215–235.
12. **Euler, L.** (1758). *Elementa doctrinae solidorum*. Novi Commentarii Academiae Scientiarum Petropolitanae, 4, 109–140.
13. **Fisk, S.** (1978). *A short proof of Chvátal's watchman theorem*. Journal of Combinatorial Theory, Series B, 24(3), 374.
14. **Gallai, T.** (1944). *Solution to Problem 4065*. The American Mathematical Monthly, 51(3), 169–171.
15. **Graham, R. L., & Pollak, H. O.** (1971). *On the addressing problem for loop switching*. Bell System Technical Journal, 50(8), 2495–2519.
16. **Hall, P.** (1935). *On representatives of subsets*. Journal of the London Mathematical Society, 10(1), 26–30.
17. **Halmos, P. R., & Vaughan, H. E.** (1950). *The marriage problem*. American Journal of Mathematics, 72(1), 214–215.
18. **Helly, E.** (1923). *Über Mengen konvexer Körper mit gemeinschaftlichen Punkten*. Jahresbericht der Deutschen Mathematiker-Vereinigung, 32, 175–176.
19. **Katona, G. O. H.** (1972). *A simple proof of the Erdös-Chao Ko-Rado theorem*. Journal of Combinatorial Theory, Series B, 13(2), 183–184.
20. **Kelly, L. M.** (1948). *A simple proof of the Sylvester-Gallai theorem*. In H. S. M. Coxeter, *Projective Geometry*, University of Toronto Press.
21. **Matoušek, J.** (2002). *Lectures on Discrete Geometry*. Graduate Texts in Mathematics 212, Springer.
22. **Ore, O.** (1960). *Note on Hamilton circuits*. The American Mathematical Monthly, 67(1), 55.
23. **Perles, M. A.** (1963). *A proof of Dilworth's decomposition theorem for partially ordered sets*. Israel Journal of Mathematics, 1(3), 139–145.
24. **Radon, J.** (1921). *Mengen konvexer Körper, die einen gemeinsamen Punkt enthalten*. Mathematische Annalen, 83(1-2), 113–115.
25. **Schur, I.** (1916). *Über die Kongruenz $x^m + y^m \equiv z^m \pmod p$*. Jahresbericht der Deutschen Mathematiker-Vereinigung, 25, 114–117.
26. **Sperner, E.** (1928). *Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes*. Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg, 6(1), 265–272.
27. **Sylvester, J. J.** (1893). *Mathematical Question 11851*. Educational Times, 59, 98.
28. **Tverberg, H.** (1966). *A generalization of Radon's theorem*. Journal of the London Mathematical Society, 41, 123–128.
29. **Tverberg, H.** (1982). *On the decomposition of $K_n$ into complete bipartite graphs*. Journal of Graph Theory, 6(4), 493–494.
30. **Wiedijk, F.** (2008). *Formalizing 100 Theorems*. http://www.cs.ru.nl/~freek/100/
31. **Wilf, H. S.** (1971). *The friendship theorem*. In *Combinatorial Mathematics and Its Applications*, Academic Press, 307–309.