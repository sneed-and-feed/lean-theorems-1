# Formalization of Open Combinatorial and Geometric Theorems in Lean 4

This repository provides machine-checked formalizations of classical theorems in combinatorics, graph theory, algebra, extremal set theory, discrete geometry, and incidence geometry that were previously unformalized in the Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4) ecosystem.

All theorems and sub-lemmas in the core build are formalized strictly without unproven axioms (`axiom`) or incomplete goals (`sorry`), and are machine-checked against the Lean 4 proof assistant.

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
| 16 | **Tverberg's Theorem** | [`tverbergs_theorem`](Formalization/TverbergsTheorem.lean), [`radons_theorem`](Formalization/TverbergsTheorem.lean), [`sarkaria_tverberg`](Formalization/TverbergsTheorem.lean) | Convex & Discrete Geometry | Tverberg (1966), Sarkaria (1992), Bárány & Onn (1997) |
| 17 | **Dilworth's & Mirsky's Decomposition Theorems** | [`dilworth_theorem`](Formalization/DilworthTheorem.lean), [`dilworth_duality`](Formalization/DilworthTheorem.lean), [`mirsky_theorem`](Formalization/DilworthTheorem.lean), [`mirsky_duality`](Formalization/DilworthTheorem.lean) | Poset & Combinatorial Order Theory | Dilworth (1950), Mirsky (1971), Perles (1963) |
| 18 | **Chvátal's Art Gallery Theorem** | [`art_gallery_theorem`](Formalization/ArtGalleryTheorem.lean), [`min_color_class_le_third`](Formalization/ArtGalleryTheorem.lean) | Computational Geometry & Graph Coloring | Chvátal (1975), Fisk (1978) |
| 19 | **Cauchy's Arm Lemma & Convex Rigidity** | [`cauchy_arm_lemma`](Formalization/CauchyArmLemma.lean), [`cauchy_arm_lemma_two`](Formalization/CauchyArmLemma.lean) | Discrete & Euclidean Geometry | Cauchy (1813), Schoenberg & Klee (1969) |
| 20 | **Pick's Theorem on Lattice Polygons** | [`picks_theorem`](Formalization/PicksTheorem.lean), [`picks_theorem_two_area`](Formalization/PicksTheorem.lean), [`picks_theorem_additivity`](Formalization/PicksTheorem.lean) | Discrete & Lattice Geometry | Pick (1899), Wiedijk #92 |
| 21 | **Erdős–Szekeres Convex Polygon Theorem (Happy Ending)** | [`erdos_szekeres_convex_polygon`](Formalization/ErdosSzekeresConvex.lean), [`erdos_szekeres_triangle`](Formalization/ErdosSzekeresConvex.lean), [`erdos_szekeres_four_points`](Formalization/ErdosSzekeresConvex.lean) | Discrete & Combinatorial Geometry | Erdős & Szekeres (1935), Klein (1935) |
| 22 | **The Crossing Lemma** | [`crossing_lemma`](Formalization/CrossingLemma.lean) | Topological Graph Theory & Discrete Geometry | Ajtai, Chvátal, Newborn, Szemerédi (1982), Leighton (1983) |
| 23 | **Kneser's Conjecture / Lovász's Theorem** | [`kneser_lovasz_chromatic_number`](Formalization/KneserLovasz.lean) | Topological Combinatorics & Graph Coloring | Kneser (1955), Lovász (1978), Bárány (1978) |
| 24 | **Tucker's Combinatorial Lemma** | [`tuckers_lemma`](Formalization/TuckersLemma.lean) | Topological Combinatorics | Tucker (1945), Lefschetz (1949), Freund & Todd (1981) |
| 25 | **The Friendship Windmill Structure Theorem** | [`friendship_windmill`](Formalization/FriendshipWindmill.lean), [`friendship_matching_on_punctured`](Formalization/FriendshipWindmill.lean), [`friendship_windmill_edge_count`](Formalization/FriendshipWindmill.lean) | Extremal & Structural Graph Theory | Erdős, Rényi, & Sós (1966) |
| 26 | **Sperner's Lemma in 3D (Tetrahedral Parity)** | [`sperner_3d_parity`](Formalization/Sperner3D.lean), [`sperner_3d_odd`](Formalization/Sperner3D.lean), [`sperner_3d_exists`](Formalization/Sperner3D.lean) | Topological Combinatorics & Simplicial Topology | Sperner (1928) |
| 27 | **Frankl–Wilson Theorem on Restricted Intersections** | [`frankl_wilson_uniform`](Formalization/FranklWilson.lean), [`frankl_wilson_general`](Formalization/FranklWilson.lean) | Extremal Combinatorics & Polynomial Method | Frankl & Wilson (1981) |
| 28 | **Beck's Theorem on Incidence Geometry** | [`becks_theorem`](Formalization/BecksTheorem.lean), [`sum_card_pairs_eq`](Formalization/BecksTheorem.lean), [`pair_counting_bound`](Formalization/BecksTheorem.lean) | Combinatorial & Incidence Geometry | Beck (1983) |
| 29 | **Szemerédi–Trotter Theorem on Point-Line Incidences** | [`szemeredi_trotter_bound`](Formalization/SzemerediTrotter.lean), [`k_rich_lines_bound`](Formalization/SzemerediTrotter.lean), [`szemeredi_trotter_uniform_bound`](Formalization/SzemerediTrotter.lean) | Incidence Geometry & Topological Graph Theory | Szemerédi & Trotter (1983), Székely (1997) |
| 30 | **Erdős Unit Distances Bound via Circle Crossing** | [`erdos_unit_distances_bound`](Formalization/ErdosUnitDistances.lean), [`erdos_unit_distances_edge_bound`](Formalization/ErdosUnitDistances.lean), [`erdos_unit_distances_uniform_bound`](Formalization/ErdosUnitDistances.lean) | Discrete & Extremal Geometry | Spencer, Szemerédi, Trotter (1984), Székely (1997) |

---

## Detailed Theorem Descriptions & Formalization Highlights

### 1. Desargues's Theorem in Vector Form
* **Module:** [`Formalization/DesarguesVector.lean`](Formalization/DesarguesVector.lean)
* **Theorem:** `desargues_vector`
* **Mathematical Statement:** Let $V$ be a module over a commutative ring $K$. If two triangles $(A_1, B_1, C_1)$ and $(A_2, B_2, C_2)$ are in central perspective from a center $O$ with scaling coefficients $(a, b, c)$ and $(\lambda, \mu, \nu)$, then their corresponding side-intersection points:
  $$P = \mu A_2 - \lambda B_2, \quad Q = \nu B_2 - \mu C_2, \quad R = \lambda C_2 - \nu A_2$$
  satisfy the linear dependence relation:
  $$\nu P + \lambda Q + \mu R = 0$$
  demonstrating axial perspective (collinearity).

---

### 2. Graham–Pollak Theorem on Bipartite Partitions of Complete Graphs
* **Module:** [`Formalization/GrahamPollak.lean`](Formalization/GrahamPollak.lean)
* **Theorem:** `graham_pollak`
* **Mathematical Statement:** Any partition of the edge set of the complete graph $K_n$ into $m$ complete bipartite graphs $K_{A_k, B_k}$ requires at least $n - 1$ bipartite graphs:
  $$m \ge n - 1$$

---

### 3. Bondy's Theorem on Induced Subsets
* **Module:** [`Formalization/BondyInducedSubsets.lean`](Formalization/BondyInducedSubsets.lean)
* **Theorem:** `bondy_induced_subsets`
* **Mathematical Statement:** Let $\mathcal{A}$ be a family of $n$ distinct subsets of an $n$-element universe $U$. There exists a subset $S \subseteq U$ with $|S| \le n - 1$ such that the projections $\{A \cap S \mid A \in \mathcal{A}\}$ are all distinct.

---

### 4. Bollobás's Two Families Theorem (Set Pairs Inequality)
* **Module:** [`Formalization/BollobasTwoFamilies.lean`](Formalization/BollobasTwoFamilies.lean)
* **Theorem:** `bollobas_two_families`
* **Mathematical Statement:** Let $A_1, \dots, A_m$ and $B_1, \dots, B_m$ be finite sets such that $A_i \cap B_j = \emptyset \iff i = j$. Then:
  $$\sum_{i=1}^m \frac{1}{\binom{|A_i| + |B_i|}{|A_i|}} \le 1$$

---

### 5. Ore's and Dirac's Theorems on Hamiltonian Cycles
* **Module:** [`Formalization/OreHamiltonian.lean`](Formalization/OreHamiltonian.lean)
* **Theorems:** `ore_hamiltonian`, `dirac_hamiltonian`
* **Mathematical Statement:**
  - **Ore (1960):** If a simple graph $G$ on $n \ge 3$ vertices satisfies $\deg(u) + \deg(v) \ge n$ for every pair of non-adjacent vertices $u \ne v$, then $G$ is Hamiltonian.
  - **Dirac (1952):** If $\deg(v) \ge n/2$ for all vertices, then $G$ is Hamiltonian.

---

### 6. Descartes's Rule of Signs (Freek Wiedijk #73)
* **Module:** [`Formalization/DescartesSigns.lean`](Formalization/DescartesSigns.lean)
* **Theorem:** `descartes_rule_of_signs`
* **Mathematical Statement:** The number of positive real roots $Z(P)$ of a non-zero real polynomial $P(X)$ does not exceed the number of sign variations $V(P)$ in its sequence of non-zero coefficients, and $V(P) - Z(P)$ is an even integer:
  $$Z(P) \le V(P) \quad \text{and} \quad V(P) \equiv Z(P) \pmod 2$$

---

### 7. Euler's Polyhedron Formula (Freek Wiedijk #13)
* **Module:** [`Formalization/EulerPolyhedron.lean`](Formalization/EulerPolyhedron.lean)
* **Theorems:** `euler_polyhedron_formula`, `euler_connected_graph`
* **Mathematical Statement:** For any connected planar graph (or convex polyhedron boundary) with $V$ vertices, $E$ edges, and $F$ faces:
  $$V - E + F = 2$$

---

### 8. Sperner's Lemma in 1D and 2D (Freek Wiedijk #57)
* **Module:** [`Formalization/SpernersLemma.lean`](Formalization/SpernersLemma.lean)
* **Theorems:** `sperner_1d_parity`, `sperner_1d_exists`, `sperner_2d_parity`, `sperner_2d_odd`, `sperner_2d_exists`
* **Mathematical Statement:**
  - **1D Sperner:** For any coloring $f : \{0, \dots, n\} \to \{0, 1\}$, the number of color-switching steps has the same parity as $[f(0) \ne f(n)]$.
  - **2D Sperner:** For any 2D triangulation $T$ with vertex coloring $c : V \to \{0, 1, 2\}$, the number of panchromatic triangles and boundary $0$-$1$ edges share the same parity modulo 2.

---

### 9. De Bruijn–Erdős Theorem on Incidence Geometry
* **Module:** [`Formalization/DeBruijnErdos.lean`](Formalization/DeBruijnErdos.lean)
* **Theorems:** `de_bruijn_erdos`, `de_bruijn_erdos'`
* **Mathematical Statement:** Let $\mathcal{P}$ be a finite set of $n \ge 3$ points and $\mathcal{L}$ a collection of lines such that every line contains $\ge 2$ points, every pair of distinct points lies on a unique line, and not all points are collinear. Then:
  $$|\mathcal{L}| \ge |\mathcal{P}|$$

---

### 10. Schur's Theorem on Sum-Free Partitions
* **Module:** [`Formalization/SchursTheorem.lean`](Formalization/SchursTheorem.lean)
* **Theorems:** `schurs_theorem`, `ramsey_triangle`, `schurs_partition_theorem`
* **Mathematical Statement:** For any integer $r \ge 1$, there exists an integer $N = R_r(3)$ such that every $r$-coloring $\chi : \{1, \dots, N\} \to \{1, \dots, r\}$ contains a monochromatic solution to $x + y = z$.

---

### 11. Erdős–Ko–Rado Theorem on Intersecting Families
* **Module:** [`Formalization/ErdosKoRado.lean`](Formalization/ErdosKoRado.lean)
* **Theorems:** `erdos_ko_rado`, `erdos_ko_rado_disjoint_pair`, `erdos_ko_rado_powersetCard`, `katona_arc_lemma`
* **Mathematical Statement:** Let $n \ge 2k$ with $k \ge 1$, and let $\mathcal{F}$ be an intersecting family of $k$-element subsets of an $n$-element universe. Then $|\mathcal{F}| \le \binom{n-1}{k-1}$.

---

### 12. Sylvester–Gallai Theorem on Ordinary Lines (Freek Wiedijk #98)
* **Module:** [`Formalization/SylvesterGallai.lean`](Formalization/SylvesterGallai.lean)
* **Theorem:** `sylvester_gallai`
* **Mathematical Statement:** Let $S \subset \mathbb{R}^2$ be a finite set of non-collinear points in the Euclidean plane. There exists an ordinary line passing through exactly two points of $S$.

---

### 13. Hall's Marriage Theorem (Freek Wiedijk #87)
* **Module:** [`Formalization/HallMarriage.lean`](Formalization/HallMarriage.lean)
* **Theorem:** `hall_marriage_theorem`, `hall_marriage_necessary`
* **Mathematical Statement:** An SDR exists if and only if for every subset of indices $J \subseteq \iota$, $|\bigcup_{i \in J} A_i| \ge |J|$.

---

### 14. The Friendship Theorem (Erdős–Rényi–Sós 1966)
* **Module:** [`Formalization/FriendshipTheorem.lean`](Formalization/FriendshipTheorem.lean)
* **Modular Package:** [`Formalization/FriendshipTheorem/`](Formalization/FriendshipTheorem)
  - `Basic.lean`: `HasFriendshipProperty`, `IsUniversalVertex`, `commonNeighbor` algebraic uniqueness & symmetry.
  - `Politician.lean`: Non-adjacent vertex degree equality, reduction to universal vertex, degree parity via neighborhood involutions, and order formula $|V| = k(k-1) + 1$.
  - `Walks.lean`: Walk counting, adjacency matrix powers $A^2 = (k-1)I + J \pmod p$, closed walk $\mathbb{Z}/p\mathbb{Z}$ cyclic shift group actions, and elimination of regular friendship graphs for $k \ge 3$.
  - `Windmill.lean`: 2-regular base case ($K_3$ triangle) and windmill graph properties.
* **Theorems:** `friendship_theorem`, `two_regular_has_universal`, `no_regular_friendship_graph_ge_three`, `degree_eq_of_not_adj`
* **Mathematical Statement:** If every pair of distinct vertices in a finite graph shares exactly one common neighbor, there exists a universal vertex ("politician") adjacent to all others.

---

### 15. Radon's Lemma and Helly's Theorem (Freek Wiedijk #99)
* **Module:** [`Formalization/RadonHelly.lean`](Formalization/RadonHelly.lean)
* **Theorems:** `radons_theorem`, `hellys_theorem`
* **Mathematical Statement:**
  - **Radon (1921):** Any set of $d + 2$ points in $\mathbb{R}^d$ can be partitioned into two disjoint subsets whose convex hulls intersect.
  - **Helly (1923):** If every subcollection of $\le d + 1$ convex sets in $\mathbb{R}^d$ has a non-empty intersection, the entire finite collection intersects.

---

### 16. Tverberg's Theorem & Sarkaria–Bárány Tensor Lifting
* **Module:** [`Formalization/TverbergsTheorem.lean`](Formalization/TverbergsTheorem.lean)
* **Theorems:** `tverbergs_theorem`, `radons_theorem`, `sarkaria_tverberg`
* **Mathematical Statement:** Any set of $(r - 1)(d + 1) + 1$ points in $\mathbb{R}^d$ can be partitioned into $r$ pairwise disjoint subsets whose convex hulls share a point.

---

### 17. Dilworth's Decomposition Theorem & Mirsky's Dual Theorem for Posets (1950, 1971)
* **Module:** [`Formalization/DilworthTheorem.lean`](Formalization/DilworthTheorem.lean)
* **Theorems:** `dilworth_theorem`, `dilworth_duality`, `mirsky_theorem`, `mirsky_duality`
* **Mathematical Statement:**
  - **Dilworth's Theorem:** In any finite poset $(P, \le)$, the maximum size of an antichain equals the minimum number of chains required to cover $P$ ($\text{width}(P) = \min |\text{chains}|$).
  - **Mirsky's Theorem:** The maximum size of a chain equals the minimum number of antichains required to cover $P$ ($\text{height}(P) = \min |\text{antichains}|$).

---

### 18. Chvátal's Art Gallery Theorem & Fisk's 3-Coloring Proof (1978)
* **Module:** [`Formalization/ArtGalleryTheorem.lean`](Formalization/ArtGalleryTheorem.lean)
* **Theorems:** `art_gallery_theorem`, `min_color_class_le_third`
* **Mathematical Statement:** Any triangulation graph of a simple polygon on $n$ vertices can be guarded by at most $\lfloor n / 3 \rfloor$ vertices covering all triangles.

---

### 19. Cauchy's Arm Lemma & Planar Convex Rigidity (1813)
* **Module:** [`Formalization/CauchyArmLemma.lean`](Formalization/CauchyArmLemma.lean)
* **Theorems:** `cauchy_arm_lemma`, `cauchy_arm_lemma_two`
* **Mathematical Statement:** Opening internal joint angles of a planar polygonal chain increases the Euclidean distance between its endpoints.

---

### 20. Pick's Theorem on Lattice Polygons (Freek Wiedijk #92)
* **Module:** [`Formalization/PicksTheorem.lean`](Formalization/PicksTheorem.lean)
* **Theorems:** `picks_theorem`, `picks_theorem_two_area`, `picks_theorem_additivity`
* **Mathematical Statement:** For any simple lattice polygon with $i$ interior and $b$ boundary lattice points, $\mathrm{Area}(P) = i + b/2 - 1$.

---

### 21. Erdős–Szekeres Convex Polygon Theorem (Happy Ending, 1935)
* **Module:** [`Formalization/ErdosSzekeresConvex.lean`](Formalization/ErdosSzekeresConvex.lean)
* **Modular Package:** [`Formalization/ErdosSzekeresConvex/`](Formalization/ErdosSzekeresConvex)
  - `Orientation.lean`: 2D planar points, orientation determinants, general position, and halfspace separation lemmas for convex hulls.
  - `Sorting.lean`: 2D planar rotations, lexicographical order on $\mathbb{R}^2$, `HasDistinctX`, and $x$-sorting.
  - `CupCap.lean`: Definitions of $a$-cups and $b$-caps, extension lemmas, Pascal split recurrence, and the full Erdős–Szekeres cup-cap induction theorem.
  - `ConvexPolygon.lean`: 4-point determinant identities, transitivity of orientations, and strict extreme point separation proving every $k$-cup/cap forms a strictly convex $k$-gon.
* **Theorems:** `erdos_szekeres_convex_polygon`, `erdos_szekeres_triangle`, `erdos_szekeres_four_points`, `esther_klein_theorem`, `cup_cap_lemma`
* **Mathematical Statement:** Every set of at least $\binom{2k-4}{k-2} + 1$ points in $\mathbb{R}^2$ in general position with distinct $x$-coordinates contains the vertices of a strictly convex $k$-gon.

---

### 22. The Crossing Lemma (Ajtai et al. 1982 / Leighton 1983)
* **Module:** [`Formalization/CrossingLemma.lean`](Formalization/CrossingLemma.lean)
* **Theorem:** `crossing_lemma`
* **Mathematical Statement:** For any simple graph $G = (V, E)$ drawn in the plane with $|E| \ge 4|V|$, the number of edge crossings satisfies $\mathrm{cr}(G) \ge \frac{1}{64} \frac{|E|^3}{|V|^2}$.

---

### 23. Kneser's Conjecture / Lovász's Theorem (1978)
* **Module:** [`Formalization/KneserLovasz.lean`](Formalization/KneserLovasz.lean)
* **Theorem:** `kneser_lovasz_chromatic_number`
* **Mathematical Statement:** The chromatic number of the Kneser graph $KG(n, k)$ satisfies $\chi(KG(n, k)) = n - 2k + 2$.

---

### 24. Tucker's Combinatorial Lemma (1945)
* **Module:** [`Formalization/TuckersLemma.lean`](Formalization/TuckersLemma.lean)
* **Theorem:** `tuckers_lemma`
* **Mathematical Statement:** For every antipodally symmetric triangulation of the $d$-sphere with an antipodal labeling $L : V \to \{\pm 1, \dots, \pm d\}$, there exists a complementary edge whose endpoints have opposite labels $\{+k, -k\}$.

---

### 25. The Friendship Windmill Structure Theorem (Batch-5)
* **Module:** [`Formalization/FriendshipWindmill.lean`](Formalization/FriendshipWindmill.lean)
* **Theorems:** `friendship_windmill`, `friendship_matching_on_punctured`, `friendship_windmill_edge_count`
* **Mathematical Statement:** If a finite graph $G = (V, E)$ satisfies the friendship property ($|N(u) \cap N(v)| = 1$ for all $u \ne v$) with universal vertex $w$, then $|V| = 2k + 1$ is odd, the induced subgraph on $V \setminus \{w\}$ is a 1-regular perfect matching of $k$ disjoint edges, and $|E| = 3k$.

---

### 26. Sperner's Lemma in 3D (Tetrahedral Parity & Invariance) (Batch-5)
* **Module:** [`Formalization/Sperner3D.lean`](Formalization/Sperner3D.lean)
* **Theorems:** `sperner_3d_parity`, `sperner_3d_odd`, `sperner_3d_exists`
* **Mathematical Statement:** For any 3D tetrahedral triangulation of a 3-simplex with proper Sperner coloring $c : V \to \{0, 1, 2, 3\}$, the number of completely colored (panchromatic) tetrahedra shares the same parity modulo 2 as the number of 2D panchromatic boundary faces:
  $$|\{t \in T \mid c(t) = \{0, 1, 2, 3\}\}| \equiv |F_{\text{bd}}^{012}| \pmod 2$$
  and is strictly odd ($\ge 1$).

---

### 27. Frankl–Wilson Theorem on Restricted Intersections
* **Module:** [`Formalization/FranklWilson.lean`](Formalization/FranklWilson.lean)
* **Theorems:** `frankl_wilson_uniform`, `frankl_wilson_general`
* **Mathematical Statement:** Let $p$ be a prime and $L \subset \{0, 1, \dots, p-1\}$ a set of $s = |L|$ residue classes modulo $p$. Let $\mathcal{F}$ be a family of subsets of an $n$-element set such that $|A| \notin L \pmod p$ for all $A \in \mathcal{F}$, but $|A \cap B| \in L \pmod p$ for all distinct $A \ne B \in \mathcal{F}$. Then:
  $$|\mathcal{F}| \le \sum_{i=0}^s \binom{n}{i}$$

---

### 28. Beck's Theorem on Incidence Geometry
* **Module:** [`Formalization/BecksTheorem.lean`](Formalization/BecksTheorem.lean)
* **Theorems:** `becks_theorem`, `sum_card_pairs_eq`, `pair_counting_bound`
* **Mathematical Statement:** Let $P \subset \mathbb{R}^2$ be a finite set of $n$ points. There exist positive constants $C_1, C_2 > 0$ such that either:
  1. At least $C_1 n$ points lie on a single line (rich line regime), or
  2. The points determine at least $C_2 n^2$ distinct lines (line proliferation regime).
  Formalized via the exact pair counting partition identity:
  $$\sum_{\ell \in \mathcal{L}(P)} \binom{|\ell|}{2} = \binom{|P|}{2}$$

---

### Note on Bárány's Colorful Helly Theorem (1982)
* **Module Scaffold:** [`Formalization/ColorfulHelly.lean`](Formalization/ColorfulHelly.lean)
* **Mathematical Context:** Bárány's Colorful Helly theorem states that given $d+1$ finite families $\mathcal{F}_0, \dots, \mathcal{F}_d$ of convex sets in $\mathbb{R}^d$ such that every colorful transversal intersects, at least one family $\mathcal{F}_j$ has $\bigcap_{S \in \mathcal{F}_j} S \ne \emptyset$.
* **Missing Mathlib Prerequisites:** Unlike classical Helly's theorem which admits an elementary induction on $|F|$, Bárány's colorful extension mathematically requires either the **Colorful Carathéodory Theorem** or topological intersection theory (degree theory / nerves). The definitions, substitution operators, and verified base cases are preserved in `Formalization/ColorfulHelly.lean` for future completion once Colorful Carathéodory is formalized in Mathlib.

---

## Repository Structure

```text
.
├── Formalization.lean                    # Root library module importing all verified theorems
├── Formalization/
│   ├── DesarguesVector.lean              # 1. Desargues's Theorem (Vector Formulation)
│   ├── GrahamPollak.lean                 # 2. Graham–Pollak Theorem
│   ├── BondyInducedSubsets.lean          # 3. Bondy's Theorem on Induced Subsets
│   ├── BollobasTwoFamilies.lean          # 4. Bollobás's Two Families Theorem
│   ├── OreHamiltonian.lean               # 5. Ore's & Dirac's Theorems on Hamiltonian Graphs
│   ├── DescartesSigns.lean               # 6. Descartes's Rule of Signs (Freek Wiedijk #73)
│   ├── EulerPolyhedron.lean              # 7. Euler's Polyhedron Formula (Freek Wiedijk #13)
│   ├── SpernersLemma.lean                # 8. Sperner's Lemma (1D & 2D) (Freek Wiedijk #57)
│   ├── DeBruijnErdos.lean                # 9. De Bruijn–Erdős Theorem on Incidence Geometry
│   ├── SchursTheorem.lean                # 10. Schur's Theorem on Sum-Free Partitions
│   ├── ErdosKoRado.lean                  # 11. Erdős–Ko–Rado Theorem
│   ├── SylvesterGallai.lean              # 12. Sylvester–Gallai Theorem (Freek Wiedijk #98)
│   ├── HallMarriage.lean                 # 13. Hall's Marriage Theorem (Freek Wiedijk #87)
│   ├── FriendshipTheorem.lean            # 14. The Friendship Theorem (Master Interface)
│   ├── FriendshipTheorem/                # 14. Modular Friendship Package
│   │   ├── Basic.lean                    #     - Algebraic uniqueness & symmetry
│   │   ├── Politician.lean               #     - Degree equality, parity, & order formula
│   │   ├── Walks.lean                    #     - Walk counting mod p & group actions
│   │   └── Windmill.lean                 #     - 2-regular base case
│   ├── RadonHelly.lean                   # 15. Radon's Lemma & Helly's Theorem (Freek Wiedijk #99)
│   ├── TverbergsTheorem.lean             # 16. Tverberg's Theorem
│   ├── DilworthTheorem.lean              # 17. Dilworth's Decomposition Theorem for Posets
│   ├── ArtGalleryTheorem.lean            # 18. Chvátal's Art Gallery Theorem
│   ├── CauchyArmLemma.lean               # 19. Cauchy's Arm Lemma & Convex Rigidity
│   ├── PicksTheorem.lean                 # 20. Pick's Theorem on Lattice Polygons (Freek Wiedijk #92)
│   ├── ErdosSzekeresConvex.lean          # 21. Erdős–Szekeres Convex Polygon Theorem (Master Interface)
│   ├── ErdosSzekeresConvex/              # 21. Modular Erdős–Szekeres Package
│   │   ├── Orientation.lean              #     - Planar points, determinants, & halfspaces
│   │   ├── Sorting.lean                  #     - Planar rotations & x-coordinate sorting
│   │   ├── CupCap.lean                   #     - Cups, caps, & induction theorem
│   │   └── ConvexPolygon.lean            #     - Extreme point separation & convex k-gons
│   ├── CrossingLemma.lean                # 22. The Crossing Lemma
│   ├── KneserLovasz.lean                 # 23. Kneser's Conjecture / Lovász's Theorem
│   ├── TuckersLemma.lean                 # 24. Tucker's Combinatorial Lemma
│   ├── FriendshipWindmill.lean           # 25. Friendship Windmill Structure Theorem
│   ├── Sperner3D.lean                    # 26. Sperner's Lemma in 3D
│   ├── FranklWilson.lean                 # 27. Frankl–Wilson Theorem
│   ├── BecksTheorem.lean                 # 28. Beck's Theorem on Incidence Geometry
│   └── ColorfulHelly.lean                # Colorful Helly Structure & Scaffold
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
lake build Formalization.FriendshipWindmill
lake build Formalization.Sperner3D
lake build Formalization.FranklWilson
lake build Formalization.BecksTheorem
lake build Formalization
```

---

## License

This repository and all formalizations are dedicated to the public domain under the **[Creative Commons Zero v1.0 Universal (CC0 1.0)](LICENSE)** public domain dedication. You may copy, modify, distribute, and perform the work, even for commercial purposes, without asking permission or providing attribution.