# Formalization of Open Combinatorial and Geometric Theorems in Lean 4

This repository provides machine-checked formalizations of classical theorems in combinatorics, graph theory, algebra, extremal set theory, discrete geometry, and incidence geometry, not found in an exact declaration, docstring, and signature search of the pinned Mathlib revision (v4.34.0-rc1 / `leanprover-community/mathlib4` git commit in `lakefile.toml`).

The primary declarations listed below and their proof dependencies are machine-checked without
project-specific axioms or incomplete goals (`sorry`). Two generic upper-bound extensions in
`ErdosKoRado.lean`—the EKR equality case and the Hilton–Milner theorem—remain explicit open targets.
Their `k = 1` and `k = 2` base cases, respectively, and the sharp Hilton–Milner extremal
construction with its exact cardinality are fully proved.

---

## Table of Theorems

| # | Theorem | Primary Declaration | Mathematical Domain | Reference |
| :---: | :--- | :--- | :--- | :--- |
| 1 | **Desargues's Theorem: Vector Identity & Proper Projective Converse** | [`desargues_vector`](Formalization/DesarguesVector.lean), [`desargues_converse_projective_plane`](Formalization/DesarguesVector.lean) | Projective & Affine Geometry | Bosse/Desargues (1647/1648), Coghetto (2021), Wiedijk #53 |
| 2 | **Graham–Pollak Theorem** | [`graham_pollak`](Formalization/GrahamPollak.lean) | Algebraic Combinatorics | Graham & Pollak (1971), Tverberg (1982) |
| 3 | **Bondy's Theorem on Induced Subsets** | [`bondy_induced_subsets`](Formalization/BondyInducedSubsets.lean) | Extremal Set Theory & VC Theory | Bondy (1972) |
| 4 | **Bollobás's Two Families Theorem** | [`bollobas_two_families`](Formalization/BollobasTwoFamilies.lean) | Extremal Combinatorics | Bollobás (1965) |
| 5 | **Ore's & Dirac's Theorems** | [`ore_hamiltonian`](Formalization/OreHamiltonian.lean), [`dirac_hamiltonian`](Formalization/OreHamiltonian.lean) | Structural Graph Theory | Ore (1960), Dirac (1952) |
| 6 | **Descartes's Rule of Signs** | [`descartes_rule_of_signs`](Formalization/DescartesSigns.lean) | Real Algebraic Geometry & Polynomials | Descartes (1637), Wiedijk #73 |
| 7 | **Euler's Polyhedron Formula** | [`euler_polyhedron_formula`](Formalization/EulerPolyhedron.lean), [`planar_edge_bound`](Formalization/EulerPolyhedron.lean), [`non_planarity_k5`](Formalization/EulerPolyhedron.lean), [`non_planarity_k33`](Formalization/EulerPolyhedron.lean) | Combinatorial Graph Theory & Discrete Geometry | Euler (1758), Cauchy (1813), Wiedijk #13 |
| 8 | **Sperner's Lemma (1D & 2D)** | [`sperner_1d_parity`](Formalization/SpernersLemma.lean), [`sperner_2d_parity`](Formalization/SpernersLemma.lean), [`sperner_2d_exists`](Formalization/SpernersLemma.lean) | Topological Combinatorics & Fixed Point Theory | Sperner (1928), Wiedijk #57 |
| 9 | **De Bruijn–Erdős Theorem on Incidence Geometry & Near-Pencil Tightness** | [`de_bruijn_erdos`](Formalization/DeBruijnErdos.lean), [`de_bruijn_erdos_tight`](Formalization/DeBruijnErdos.lean) | Incidence Geometry & Extremal Combinatorics | De Bruijn & Erdős (1948) |
| 10 | **Schur's Theorem on Sum-Free Partitions** | [`schurs_theorem`](Formalization/SchursTheorem.lean), [`ramsey_triangle`](Formalization/SchursTheorem.lean) | Ramsey Theory & Additive Combinatorics | Schur (1916) |
| 11 | **Erdős–Ko–Rado, Small-Parameter Stability, and Hilton–Milner Sharpness** | [`erdos_ko_rado`](Formalization/ErdosKoRado.lean), [`erdos_ko_rado_uniqueness_one`](Formalization/ErdosKoRado.lean), [`hilton_milner_stability_two`](Formalization/ErdosKoRado.lean), [`exists_hiltonMilner_extremizer`](Formalization/ErdosKoRado.lean) | Extremal Set Theory & Combinatorics | Erdős, Ko, & Rado (1961), Hilton & Milner (1967), Katona (1972) |
| 12 | **Sylvester–Gallai Theorem** | [`sylvester_gallai`](Formalization/SylvesterGallai.lean) | Incidence & Euclidean Geometry | Sylvester (1893), Gallai (1944), Kelly (1948), Wiedijk #98 |
| 13 | **Hall's Marriage Theorem** | [`hall_marriage_theorem`](Formalization/HallMarriage.lean) | Combinatorial Matching Theory | Hall (1935), Halmos & Vaughan (1950), Wiedijk #87 |
| 14 | **The Friendship Theorem** | [`friendship_theorem`](Formalization/FriendshipTheorem.lean) | Extremal & Spectral Graph Theory | Erdős, Rényi, & Sós (1966), Wilf (1971) |
| 15 | **Radon's Lemma & Helly's Theorem** | [`radons_theorem`](Formalization/RadonHelly.lean), [`hellys_theorem`](Formalization/RadonHelly.lean) | Convex & Discrete Geometry | Radon (1921), Helly (1923), Wiedijk #99 |
| 16 | **Tverberg's Theorem (Classical, Full 1D, & 1D Colorful Tverberg)** | [`tverbergs_theorem`](Formalization/TverbergsTheorem.lean), [`tverberg_1d`](Formalization/TverbergsTheorem.lean), [`tverberg_1d_of_card_ge`](Formalization/TverbergsTheorem.lean), [`colorful_tverberg_1d`](Formalization/TverbergsTheorem.lean), [`sarkaria_tverberg`](Formalization/TverbergsTheorem.lean) | Convex & Discrete Geometry | Tverberg (1966), Bárány, Larman, Pach (1992), Sarkaria (1992) |
| 17 | **Dilworth's & Mirsky's Decomposition Theorems** | [`dilworth_theorem`](Formalization/DilworthTheorem.lean), [`dilworth_duality`](Formalization/DilworthTheorem.lean), [`mirsky_theorem`](Formalization/DilworthTheorem.lean), [`mirsky_duality`](Formalization/DilworthTheorem.lean) | Poset & Combinatorial Order Theory | Dilworth (1950), Mirsky (1971), Perles (1963) |
| 18 | **Chvátal's Art Gallery Theorem** | [`art_gallery_theorem`](Formalization/ArtGalleryTheorem.lean), [`min_color_class_le_third`](Formalization/ArtGalleryTheorem.lean) | Computational Geometry & Graph Coloring | Chvátal (1975), Fisk (1978) |
| 19 | **Cauchy's Arm Lemma & Convex Rigidity** | [`cauchy_arm_lemma`](Formalization/CauchyArmLemma.lean), [`cauchy_arm_lemma_two`](Formalization/CauchyArmLemma.lean) | Discrete & Euclidean Geometry | Cauchy (1813), Schoenberg & Klee (1969) |
| 20 | **Pick's Theorem on Lattice Polygons** | [`picks_theorem`](Formalization/PicksTheorem.lean), [`picks_theorem_two_area`](Formalization/PicksTheorem.lean), [`picks_theorem_additivity`](Formalization/PicksTheorem.lean) | Discrete & Lattice Geometry | Pick (1899), Wiedijk #92 |
| 21 | **Erdős–Szekeres Convex Polygon Theorem (Happy Ending)** | [`erdos_szekeres_convex_polygon`](Formalization/ErdosSzekeresConvex.lean), [`erdos_szekeres_triangle`](Formalization/ErdosSzekeresConvex.lean), [`erdos_szekeres_four_points`](Formalization/ErdosSzekeresConvex.lean) | Discrete & Combinatorial Geometry | Erdős & Szekeres (1935), Klein (1935) |
| 22 | **The Crossing Lemma** | [`crossing_lemma`](Formalization/CrossingLemma.lean) | Topological Graph Theory & Discrete Geometry | Ajtai, Chvátal, Newborn, Szemerédi (1982), Leighton (1983) |
| 23 | **Kneser's Graph Coloring Upper Bound** | [`kneser_graph_colorable`](Formalization/KneserLovasz.lean) | Combinatorics & Graph Coloring | Kneser (1955), Lovász (1978) |
| 24 | **Tucker's Combinatorial Lemma** | [`tuckers_lemma`](Formalization/TuckersLemma.lean) | Topological Combinatorics | Tucker (1945), Lefschetz (1949), Freund & Todd (1981) |
| 25 | **The Friendship Windmill Structure Theorem** | [`friendship_windmill`](Formalization/FriendshipWindmill.lean), [`friendship_matching_on_punctured`](Formalization/FriendshipWindmill.lean), [`friendship_windmill_edge_count`](Formalization/FriendshipWindmill.lean) | Extremal & Structural Graph Theory | Erdős, Rényi, & Sós (1966) |
| 26 | **General $n$-Dimensional Sperner's Lemma & Specializations** | [`sperner_nd_parity`](Formalization/SpernerND.lean), [`sperner_nd_odd`](Formalization/SpernerND.lean), [`sperner_nd_exists`](Formalization/SpernerND.lean), [`sperner_3d_parity`](Formalization/Sperner3D.lean) | Topological Combinatorics & Simplicial Topology | Sperner (1928), Kuhn (1968) |
| 27 | **Frankl–Wilson Theorem on Restricted Intersections** | [`frankl_wilson_uniform`](Formalization/FranklWilson.lean), [`frankl_wilson_general`](Formalization/FranklWilson.lean) | Extremal Combinatorics & Polynomial Method | Frankl & Wilson (1981) |
| 28 | **Beck's Theorem on Incidence Geometry** | [`sum_card_pairs_eq`](Formalization/BecksTheorem.lean), [`pair_counting_bound`](Formalization/BecksTheorem.lean), [`becks_dichotomy_parameterized`](Formalization/BecksTheorem.lean) | Combinatorial & Incidence Geometry | Beck (1983) |
| 29 | **Szemerédi–Trotter Theorem on Point-Line Incidences** | [`szemeredi_trotter_bound`](Formalization/SzemerediTrotter.lean), [`k_rich_lines_bound`](Formalization/SzemerediTrotter.lean), [`szemeredi_trotter_uniform_bound`](Formalization/SzemerediTrotter.lean) | Incidence Geometry & Topological Graph Theory | Szemerédi & Trotter (1983), Székely (1997) |
| 30 | **Erdős Unit Distances Bound via Circle Crossing** | [`erdos_unit_distances_bound`](Formalization/ErdosUnitDistances.lean), [`erdos_unit_distances_edge_bound`](Formalization/ErdosUnitDistances.lean), [`erdos_unit_distances_uniform_bound`](Formalization/ErdosUnitDistances.lean) | Discrete & Extremal Geometry | Spencer, Szemerédi, Trotter (1984), Székely (1997) |
| 31 | **Tutte's 1-Factor Theorem & Tutte–Berge Formula** | [`tutte_1factor_theorem`](Formalization/TutteOneFactor.lean), [`tutte_necessity`](Formalization/TutteOneFactor.lean), [`tutte_berge_min_eq_card_sub_defect`](Formalization/TutteOneFactor.lean), [`matchingDefect_nonpos_iff_hasOneFactor`](Formalization/TutteOneFactor.lean) | Structural Graph Theory & Factorizations | Tutte (1947), Berge (1958) |
| 32 | **Lovász's Colorful Helly Theorem (Bárány 1982 Primal-Dual Framework)** | [`colorful_helly_all_dimensions`](Formalization/ColorfulHelly.lean), [`colorful_helly`](Formalization/ColorfulHelly.lean), [`colorful_helly_inductive`](Formalization/ColorfulHelly.lean) | Convex & Discrete Geometry | Lovász (1974), first published proof: Bárány (1982) |
| 33 | **Elekes's Sum-Product Inequality** | [`elekes_product_sum_bound`](Formalization/ElekesSumProduct.lean), [`elekes_max_sum_product_bound`](Formalization/ElekesSumProduct.lean), [`elekes_productset_growth_of_small_sumset`](Formalization/ElekesSumProduct.lean) | Additive Combinatorics & Incidence Geometry | Elekes (1997), Erdős & Szemerédi (1983) |
| 34 | **Bárány's Colorful Carathéodory Theorem, Selection Lemmas, & Centerpoints** | [`colorful_caratheodory_point`](Formalization/ColorfulCaratheodory.lean), [`colorful_caratheodory_origin`](Formalization/ColorfulCaratheodory.lean), [`caratheodory_classical`](Formalization/ColorfulCaratheodory.lean), [`first_selection_lemma_1d`](Formalization/ColorfulCaratheodory.lean), [`centerpoint_1d`](Formalization/ColorfulCaratheodory.lean), [`colorful_selection_lemma_1d`](Formalization/ColorfulCaratheodory.lean) | Convex & Discrete Geometry | Bárány (1982), Carathéodory (1907), Rado (1946) |

---

## Detailed Theorem Descriptions & Formalization Highlights

### 1. Desargues's Theorem: Vector and Axiomatic Projective Forms
* **Module:** [`Formalization/DesarguesVector.lean`](Formalization/DesarguesVector.lean)
* **Theorems:** `desargues_vector`, `desargues_projective_plane_proper`, `desargues_converse_projective_plane`, `exists_centralPerspective_iff_exists_properAxialPerspective`, `axialPerspective_not_implies_central`
* **Mathematical Statement:** Let $V$ be a module over a commutative ring $K$. If two triangles $(A_1, B_1, C_1)$ and $(A_2, B_2, C_2)$ are in central perspective from a center $O$ with scaling coefficients $(a, b, c)$ and $(\lambda, \mu, \nu)$, then their corresponding side-intersection points:
  $$P = \mu A_2 - \lambda B_2, \quad Q = \nu B_2 - \mu C_2, \quad R = \lambda C_2 - \nu A_2$$
  satisfy the linear dependence relation $\nu P + \lambda Q + \mu R = 0$ demonstrating axial perspective (collinearity).

---

### 2. Graham–Pollak Theorem on Bipartite Partitions of Complete Graphs
* **Module:** [`Formalization/GrahamPollak.lean`](Formalization/GrahamPollak.lean)
* **Theorems:** `graham_pollak`, `graham_pollak_tight`
* **Mathematical Statement:** Any partition of the edge set of the complete graph $K_n$ into $m$ complete bipartite graphs $K_{A_k, B_k}$ requires at least $n - 1$ bipartite graphs ($m \ge n - 1$). The star decomposition proves this bound is sharp.

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
* **Modular Package:** [`Formalization/CombinatorialMap/`](Formalization/CombinatorialMap)
  - `Basic.lean`: Darts, edge involution $\alpha$, vertex permutation $\sigma$, and face permutation $\phi = (\sigma \alpha)^{-1}$.
  - `Parity.lean`: Tutte–Edmonds rotation systems and topological parity theorem $(-1)^{V+E+F} = 1$.
  - `Concrete.lean`: Explicit map coordinates for tetrahedron, triangle, and square.
* **Theorems:** `euler_polyhedron_formula`, `planar_edge_bound`, `planar_edge_bound_triangle_free`, `average_degree_lt_six`, `non_planarity_k5`, `non_planarity_k33`
* **Mathematical Statement:** For any connected planar map $M$, $V - E + F = 2$.

---

### 8. Sperner's Lemma in 1D and 2D (Freek Wiedijk #57)
* **Module:** [`Formalization/SpernersLemma.lean`](Formalization/SpernersLemma.lean)
* **Theorems:** `sperner_1d_parity`, `sperner_1d_exists`, `sperner_2d_parity`, `sperner_2d_odd`, `sperner_2d_exists`
* **Mathematical Statement:** 1D discrete boundary parity and 2D abstract pseudomanifold parity transfer.

---

### 9. De Bruijn–Erdős Theorem on Incidence Geometry & Near-Pencil Tightness
* **Module:** [`Formalization/DeBruijnErdos.lean`](Formalization/DeBruijnErdos.lean)
* **Theorems:** `de_bruijn_erdos`, `de_bruijn_erdos_tight`
* **Mathematical Statement:** Any non-collinear incidence configuration of $n \ge 3$ points satisfies $|\mathcal{L}| \ge |\mathcal{P}|$, with equality attained sharply by the near-pencil.

---

### 10. Schur's Theorem on Sum-Free Partitions
* **Module:** [`Formalization/SchursTheorem.lean`](Formalization/SchursTheorem.lean)
* **Theorems:** `schurs_theorem`, `ramsey_triangle`, `schurs_partition_theorem`
* **Mathematical Statement:** Every finite coloring of the integers $\{1, \dots, R_r(3)\}$ contains a monochromatic solution to $x + y = z$.

---

### 11. Erdős–Ko–Rado, Small-Parameter Stability, and Hilton–Milner Sharpness
* **Module:** [`Formalization/ErdosKoRado.lean`](Formalization/ErdosKoRado.lean)
* **Theorems:** `erdos_ko_rado`, `erdos_ko_rado_uniqueness_one`, `hilton_milner_stability_two`, `exists_hiltonMilner_extremizer`
* **Mathematical Statement:** Intersecting family size bound $|\mathcal{F}| \le \binom{n-1}{k-1}$ and sharp Hilton–Milner non-star extremizer.

---

### 12. Sylvester–Gallai Theorem on Ordinary Lines (Freek Wiedijk #98)
* **Module:** [`Formalization/SylvesterGallai.lean`](Formalization/SylvesterGallai.lean)
* **Theorem:** `sylvester_gallai`
* **Mathematical Statement:** Any finite non-collinear set in $\mathbb{R}^2$ determines an ordinary line containing exactly two points.

---

### 13. Hall's Marriage Theorem (Freek Wiedijk #87)
* **Module:** [`Formalization/HallMarriage.lean`](Formalization/HallMarriage.lean)
* **Theorems:** `hall_marriage_theorem`, `hall_marriage_necessary`
* **Mathematical Statement:** An SDR exists if and only if Hall's marriage condition $|\bigcup_{i \in J} A_i| \ge |J|$ holds for all index subsets $J$.

---

### 14. The Friendship Theorem (Erdős–Rényi–Sós 1966)
* **Module:** [`Formalization/FriendshipTheorem.lean`](Formalization/FriendshipTheorem.lean)
* **Modular Package:** [`Formalization/FriendshipTheorem/`](Formalization/FriendshipTheorem)
  - `Basic.lean`: Algebraic uniqueness & symmetry of common neighbors.
  - `Politician.lean`: Degree equality of non-adjacent vertices, parity invariants, and order formula $|V| = k(k-1)+1$.
  - `Walks.lean`: Walk counting, adjacency powers mod $p$, and cyclic group action elimination of regular friendship graphs.
  - `Windmill.lean`: 2-regular base case ($K_3$ triangle).
* **Theorems:** `friendship_theorem`, `two_regular_has_universal`, `no_regular_friendship_graph_ge_three`

---

### 15. Radon's Lemma and Helly's Theorem (Freek Wiedijk #99)
* **Module:** [`Formalization/RadonHelly.lean`](Formalization/RadonHelly.lean)
* **Theorems:** `radons_theorem`, `hellys_theorem`
* **Mathematical Statement:**
  - **Radon (1921):** Any set of $d + 2$ points in $\mathbb{R}^d$ can be partitioned into two disjoint subsets whose convex hulls intersect.
  - **Helly (1923):** If every subcollection of $\le d + 1$ convex sets in $\mathbb{R}^d$ has a non-empty intersection, the entire finite collection intersects.

---

### 16. Tverberg's Theorem: Classical Reductions, 1D Theorem, & 1D Colorful Tverberg
* **Module:** [`Formalization/TverbergsTheorem.lean`](Formalization/TverbergsTheorem.lean)
* **Modular Package:** [`Formalization/TverbergsTheorem/`](Formalization/TverbergsTheorem)
  - `Basis.lean`: Auxiliary zero-sum basis vectors (`auxVec`) and lifted affine coordinates (`liftAffine`).
  - `Sarkaria.lean`: Sarkaria's algebraic reduction lemma, tensor combinations, and $(d+2)$-point Radon partition.
  - `Dim1.lean`: Classical 1D Tverberg theorem (`tverberg_1d`, `tverberg_1d_of_card_ge`) via symmetric-rank pairing.
  - `Colorful.lean`: 1D Colorful Tverberg Theorem (`colorful_tverberg_1d`, Bárány–Larman–Pach 1992) across two color classes of size $r$.
* **Theorems:** `tverbergs_theorem`, `tverberg_1d`, `tverberg_1d_of_card_ge`, `colorful_tverberg_1d`, `sarkaria_tverberg`

---

### 17. Dilworth's & Mirsky's Decomposition Theorems for Posets (1950, 1971)
* **Module:** [`Formalization/DilworthTheorem.lean`](Formalization/DilworthTheorem.lean)
* **Theorems:** `dilworth_theorem`, `dilworth_duality`, `mirsky_theorem`, `mirsky_duality`
* **Mathematical Statement:** Width equals minimum chain cover size; height equals minimum antichain cover size.

---

### 18. Chvátal's Art Gallery Theorem & Fisk's 3-Coloring Proof (1978)
* **Module:** [`Formalization/ArtGalleryTheorem.lean`](Formalization/ArtGalleryTheorem.lean)
* **Theorems:** `art_gallery_theorem`, `min_color_class_le_third`
* **Mathematical Statement:** Any triangulated polygon on $n$ vertices can be guarded by at most $\lfloor n / 3 \rfloor$ vertices.

---

### 19. Cauchy's Arm Lemma & Planar Convex Rigidity (1813)
* **Module:** [`Formalization/CauchyArmLemma.lean`](Formalization/CauchyArmLemma.lean)
* **Theorems:** `cauchy_arm_lemma`, `cauchy_arm_lemma_two`
* **Mathematical Statement:** Opening internal joint angles of a planar polygonal chain increases endpoint distance.

---

### 20. Pick's Theorem on Lattice Polygons (Freek Wiedijk #92)
* **Module:** [`Formalization/PicksTheorem.lean`](Formalization/PicksTheorem.lean)
* **Theorems:** `picks_theorem`, `picks_theorem_two_area`, `picks_theorem_additivity`
* **Mathematical Statement:** $\text{Area}(P) = I + B/2 - 1$.

---

### 21. Erdős–Szekeres Convex Polygon Theorem (The Happy Ending Theorem, 1935)
* **Module:** [`Formalization/ErdosSzekeresConvex.lean`](Formalization/ErdosSzekeresConvex.lean)
* **Modular Package:** [`Formalization/ErdosSzekeresConvex/`](Formalization/ErdosSzekeresConvex)
  - `Orientation.lean`: Planar points, $3 \times 3$ determinant orientations, and halfspace separation.
  - `Sorting.lean`: Rotation invariance and strictly ordered $x$-coordinates.
  - `CupCap.lean`: $(k, \ell)$-cups, $(k, \ell)$-caps, and cup-cap composition induction.
  - `ConvexPolygon.lean`: Extreme points and existence of convex $k$-gons for $|S| \ge \binom{2k-4}{k-2}+1$.
* **Theorems:** `erdos_szekeres_convex_polygon`, `erdos_szekeres_triangle`, `erdos_szekeres_four_points`, `esther_klein_theorem`

---

### 22. The Crossing Lemma (Ajtai et al. 1982, Leighton 1983)
* **Module:** [`Formalization/CrossingLemma.lean`](Formalization/CrossingLemma.lean)
* **Theorem:** `crossing_lemma`
* **Mathematical Statement:** Any drawing of a simple graph with $E \ge 4V$ has at least $\text{cr}(G) \ge \frac{1}{64} \frac{E^3}{V^2}$ edge crossings.

---

### 23. Kneser's Graph Coloring Upper Bound (1955)
* **Module:** [`Formalization/KneserLovasz.lean`](Formalization/KneserLovasz.lean)
* **Theorem:** `kneser_graph_colorable`
* **Mathematical Statement:** $\chi(KG_{n,k}) \le n - 2k + 2$.

---

### 24. Tucker's Combinatorial Lemma
* **Module:** [`Formalization/TuckersLemma.lean`](Formalization/TuckersLemma.lean)
* **Theorems:** `tuckers_lemma_1d`, `tuckers_lemma`
* **Mathematical Statement:** Discrete antipode sign preservation and 1D/2D complementary edge existence.

---

### 25. The Friendship Windmill Structure Theorem (Erdős–Rényi–Sós 1966)
* **Module:** [`Formalization/FriendshipWindmill.lean`](Formalization/FriendshipWindmill.lean)
* **Theorems:** `friendship_windmill`, `friendship_matching_on_punctured`, `friendship_windmill_edge_count`
* **Mathematical Statement:** Every friendship graph is isomorphic to a windmill graph $Wd(k, 2) = K_1 \nabla (k K_2)$ consisting of $k$ triangles sharing a single central hub.

---

### 26. General $n$-Dimensional Sperner's Lemma & Specializations
* **Modules:** [`Formalization/SpernerND.lean`](Formalization/SpernerND.lean), [`Formalization/Sperner3D.lean`](Formalization/Sperner3D.lean)
* **Theorems:** `sperner_nd_parity`, `sperner_nd_odd`, `sperner_nd_exists`, `sperner_3d_parity`, `sperner_3d_odd`, `sperner_3d_exists`
* **Mathematical Statement:** General $n$-dimensional pseudomanifold boundary door-counting parity transfer.

---

### 27. Frankl–Wilson Theorem on Restricted Intersections (1981)
* **Module:** [`Formalization/FranklWilson.lean`](Formalization/FranklWilson.lean)
* **Theorems:** `frankl_wilson_uniform`, `frankl_wilson_general`
* **Mathematical Statement:** For any prime $p$ and $L$-intersecting family mod $p$, $|\mathcal{F}| \le \sum_{i=0}^{|L|} \binom{n}{i}$.

---

### 28. Beck's Theorem on Incidence Geometry (1983)
* **Module:** [`Formalization/BecksTheorem.lean`](Formalization/BecksTheorem.lean)
* **Theorems:** `sum_card_pairs_eq`, `pair_counting_bound`, `becks_dichotomy_parameterized`
* **Mathematical Statement:** Either $\Omega(n)$ points are collinear or the configuration determines $\Omega(n^2)$ distinct lines.

---

### 29. Szemerédi–Trotter Theorem on Point-Line Incidences (1983)
* **Module:** [`Formalization/SzemerediTrotter.lean`](Formalization/SzemerediTrotter.lean)
* **Theorems:** `szemeredi_trotter_bound`, `szemeredi_trotter_uniform_bound`, `k_rich_lines_bound`
* **Mathematical Statement:** $I(P, L) \le 4 (m n)^{2/3} + 4m + n$.

---

### 30. Erdős Unit Distances Bound via Circle Crossing (1984, 1997)
* **Module:** [`Formalization/ErdosUnitDistances.lean`](Formalization/ErdosUnitDistances.lean)
* **Theorems:** `erdos_unit_distances_bound`, `erdos_unit_distances_uniform_bound`, `erdos_unit_distances_global_bound`
* **Mathematical Statement:** $u(n) \le 8 n^{4/3}$ unit distances among $n$ points in $\mathbb{R}^2$.

---

### 31. Tutte's 1-Factor Theorem & Tutte–Berge Formula (1947, 1958)
* **Module:** [`Formalization/TutteOneFactor.lean`](Formalization/TutteOneFactor.lean)
* **Theorems:** `tutte_1factor_theorem`, `tutte_necessity`, `tutte_berge_min_eq_card_sub_defect`, `matchingDefect_nonpos_iff_hasOneFactor`
* **Mathematical Statement:** $G$ has a 1-factor iff $q(G \setminus U) \le |U|$ for all $U \subseteq V$.

---

### 32. Lovász's Colorful Helly Theorem & Bárány (1982) Primal-Dual Framework
* **Module:** [`Formalization/ColorfulHelly.lean`](Formalization/ColorfulHelly.lean)
* **Theorems:** `colorful_helly_all_dimensions`, `colorful_helly`, `colorful_helly_inductive`
* **Mathematical Statement:** Given $d+1$ finite families $\mathcal{F}_0, \dots, \mathcal{F}_d$ of convex sets in $\mathbb{R}^d$, if every colorful transversal intersects, then some family $\mathcal{F}_j$ has $\bigcap_{S \in \mathcal{F}_j} S \ne \emptyset$. Formulates the dual face to Bárány's Colorful Carathéodory theorem.

---

### 33. Elekes's Sum-Product Inequality (1997)
* **Module:** [`Formalization/ElekesSumProduct.lean`](Formalization/ElekesSumProduct.lean)
* **Theorems:** `elekes_product_sum_bound`, `elekes_max_sum_product_bound`, `elekes_productset_growth_of_small_sumset`
* **Mathematical Statement:** $|A + A| \cdot |A \cdot A| \ge \frac{1}{16} |A|^{5/2}$ and $\max(|A + A|, |A \cdot A|) \ge \frac{1}{4} |A|^{5/4}$.

---

### 34. Bárány's Colorful Carathéodory Theorem, Selection Lemmas, & Centerpoints (1982)
* **Module:** [`Formalization/ColorfulCaratheodory.lean`](Formalization/ColorfulCaratheodory.lean)
* **Modular Package:** [`Formalization/ColorfulCaratheodory/`](Formalization/ColorfulCaratheodory)
  - `Basic.lean`: Euclidean inner products, squared Euclidean norms, and quadratic binomial expansions.
  - `Separation.lean`: Linear functional hyperplane separation on convex hulls.
  - `Perturbation.lean`: Strictly decreasing segment distance perturbation lemmas.
  - `Transversals.lean`: Dependent choice Fintype `ColorfulChoice S`, finset `colorfulTransversals S`, and transversal coordinate updates.
  - `Dim1.lean`: Exact 1D coordinate separation and 1D colorful Carathéodory base case.
  - `Selection.lean`: 1D Centerpoint Theorem, Bárány's 1982 First Selection Lemma in 1D, and 1D Colorful Selection Lemma.
* **Theorems:** `colorful_caratheodory_point`, `colorful_caratheodory_origin`, `colorful_caratheodory_dim1`, `colorful_caratheodory_dim2`, `caratheodory_classical`, `caratheodory_classical_deduction`, `centerpoint_1d`, `first_selection_lemma_1d`, `colorful_selection_lemma_1d`
* **Mathematical Statement:**
  - **Colorful Carathéodory (Bárány 1982):** For any $d+1$ color classes $S_0, \dots, S_d \subset \mathbb{R}^d$ whose convex hulls all contain $p$, there exists a colorful transversal $f$ ($f(i) \in S_i$) such that $p \in \operatorname{conv}(\operatorname{range} f)$.
  - **1D First Selection Lemma (Bárány 1982):** Any finite set of $n \ge 2$ points in $\mathbb{R}^1$ has a median point contained in at least $\lfloor n/2 \rfloor \cdot \lceil n/2 \rceil \ge \frac{n^2 - 1}{4}$ spanned intervals ($c_1 = 1/2$).
  - **1D Centerpoint Theorem (Rado 1946):** The median point of any finite point set in $\mathbb{R}^1$ has halfspace depth $\ge \lceil (n+1)/2 \rceil$.

---

## Repository Architecture & File Diagram

```mermaid
graph TD
    Root["Formalization.lean (Master Root)"]
    
    subgraph ConvexGeometry ["Convex & Discrete Geometry"]
        CC["ColorfulCaratheodory/ (6 Submodules)"]
        CH["ColorfulHelly.lean (Primal-Dual Bridge)"]
        RH["RadonHelly.lean (Freek #99)"]
        TT["TverbergsTheorem/ (4 Submodules)"]
        ES["ErdosSzekeresConvex/ (4 Submodules)"]
        CA["CauchyArmLemma.lean"]
        PK["PicksTheorem.lean (Freek #92)"]
    end

    subgraph TopologicalCombinatorics ["Topological Combinatorics"]
        SND["SpernerND.lean (General n-D)"]
        S3D["Sperner3D.lean"]
        S12["SpernersLemma.lean (1D & 2D)"]
        TL["TuckersLemma.lean"]
        AG["ArtGalleryTheorem.lean (Fisk 3-Color)"]
        CM["CombinatorialMap/ (3 Submodules)"]
        EP["EulerPolyhedron.lean (Freek #13)"]
    end

    subgraph GraphTheory ["Structural & Extremal Graph Theory"]
        FT["FriendshipTheorem/ (4 Submodules)"]
        FW["FriendshipWindmill.lean"]
        TO["TutteOneFactor.lean (Tutte-Berge)"]
        OH["OreHamiltonian.lean (Ore & Dirac)"]
        GP["GrahamPollak.lean"]
        KL["KneserLovasz.lean"]
        CL["CrossingLemma.lean"]
    end

    subgraph IncidenceAndAdditive ["Incidence Geometry & Additive Combinatorics"]
        BE["BecksTheorem.lean"]
        ST["SzemerediTrotter.lean"]
        UD["ErdosUnitDistances.lean"]
        ESP["ElekesSumProduct.lean"]
        DBE["DeBruijnErdos.lean"]
        SG["SylvesterGallai.lean (Freek #98)"]
        DV["DesarguesVector.lean (Freek #53)"]
        SC["SchursTheorem.lean"]
        DS["DescartesSigns.lean (Freek #73)"]
        EKR["ErdosKoRado.lean"]
        BT["BollobasTwoFamilies.lean"]
        BI["BondyInducedSubsets.lean"]
        HM["HallMarriage.lean (Freek #87)"]
        DT["DilworthTheorem.lean"]
        FWI["FranklWilson.lean"]
    end

    Root --> ConvexGeometry
    Root --> TopologicalCombinatorics
    Root --> GraphTheory
    Root --> IncidenceAndAdditive
```

### Complete Filesystem Hierarchy

```text
.
├── Formalization.lean                            # Root master module importing all 34 verified theorem suites
├── Formalization/
│   ├── ArtGalleryTheorem.lean                    # 18. Chvátal's Art Gallery Theorem (Fisk 3-coloring)
│   ├── BecksTheorem.lean                         # 28. Beck's Theorem on Incidence Geometry
│   ├── BollobasTwoFamilies.lean                  # 4. Bollobás's Two Families Theorem
│   ├── BondyInducedSubsets.lean                  # 3. Bondy's Theorem on Induced Subsets
│   ├── CauchyArmLemma.lean                       # 19. Cauchy's Arm Lemma & Convex Rigidity
│   ├── ColorfulCaratheodory.lean                 # 34. Bárány's Colorful Carathéodory Theorem (Master Interface)
│   ├── ColorfulCaratheodory/                     # 34. Modular Colorful Carathéodory Package
│   │   ├── Basic.lean                            #     - Euclidean dot product & squared norm algebra
│   │   ├── Separation.lean                       #     - Hyperplane separation on convex hulls
│   │   ├── Perturbation.lean                     #     - Strictly decreasing segment perturbation
│   │   ├── Transversals.lean                     #     - Dependent choice Fintypes & transversal updates
│   │   ├── Dim1.lean                             #     - 1D coordinate pairing & base case
│   │   └── Selection.lean                        #     - 1D First Selection Lemma & Centerpoint Theorem
│   ├── ColorfulHelly.lean                        # 32. Lovász's Colorful Helly Theorem (Bárány 1982 Primal-Dual)
│   ├── CombinatorialMap/                         # 7. Combinatorial Maps (Tutte–Edmonds Rotation Systems)
│   │   ├── Basic.lean                            #     - Darts, edge involution α, vertex permutation σ, & faces φ
│   │   ├── Concrete.lean                         #     - Concrete polyhedra (tetrahedron, triangle, square maps)
│   │   └── Parity.lean                           #     - Permutation sign parity theorem: (-1)^(V+E+F) = 1
│   ├── CrossingLemma.lean                        # 22. The Crossing Lemma (Ajtai et al., Leighton)
│   ├── DeBruijnErdos.lean                        # 9. De Bruijn–Erdős Theorem on Incidence Geometry
│   ├── DesarguesVector.lean                      # 1. Desargues's Theorem (Vector & Projective Forms)
│   ├── DescartesSigns.lean                       # 6. Descartes's Rule of Signs (Freek Wiedijk #73)
│   ├── DilworthTheorem.lean                      # 17. Dilworth's & Mirsky's Decomposition Theorems for Posets
│   ├── ElekesSumProduct.lean                     # 33. Elekes's Sum-Product Inequality in Additive Combinatorics
│   ├── ErdosKoRado.lean                          # 11. Erdős–Ko–Rado Theorem & Hilton–Milner Sharpness
│   ├── ErdosSzekeresConvex.lean                  # 21. Erdős–Szekeres Convex Polygon Theorem (Master Interface)
│   ├── ErdosSzekeresConvex/                      # 21. Modular Erdős–Szekeres Package
│   │   ├── ConvexPolygon.lean                    #     - Extreme point separation & convex k-gons
│   │   ├── CupCap.lean                           #     - Cups, caps, & induction theorem
│   │   ├── Orientation.lean                      #     - Planar points, determinants, & halfspaces
│   │   └── Sorting.lean                          #     - Planar rotations & x-coordinate sorting
│   ├── ErdosUnitDistances.lean                   # 30. Erdős Unit Distances Bound (Circle Crossing)
│   ├── EulerPolyhedron.lean                      # 7. Euler's Polyhedron Formula (Freek Wiedijk #13)
│   ├── FranklWilson.lean                         # 27. Frankl–Wilson Theorem on Restricted Intersections
│   ├── FriendshipTheorem.lean                    # 14. The Friendship Theorem (Master Interface)
│   ├── FriendshipTheorem/                        # 14. Modular Friendship Package
│   │   ├── Basic.lean                            #     - Algebraic uniqueness & symmetry
│   │   ├── Politician.lean                       #     - Degree equality, parity, & order formula
│   │   ├── Walks.lean                            #     - Walk counting mod p & group actions
│   │   └── Windmill.lean                         #     - 2-regular base case
│   ├── FriendshipWindmill.lean                   # 25. Friendship Windmill Structure Theorem
│   ├── GrahamPollak.lean                         # 2. Graham–Pollak Theorem
│   ├── HallMarriage.lean                         # 13. Hall's Marriage Theorem (Freek Wiedijk #87)
│   ├── KneserLovasz.lean                         # 23. Kneser's Graph Coloring Upper Bound
│   ├── OreHamiltonian.lean                       # 5. Ore's & Dirac's Theorems on Hamiltonian Graphs
│   ├── PicksTheorem.lean                         # 20. Pick's Theorem on Lattice Polygons (Freek Wiedijk #92)
│   ├── RadonHelly.lean                           # 15. Radon's Lemma & Helly's Theorem (Freek Wiedijk #99)
│   ├── SchursTheorem.lean                        # 10. Schur's Theorem on Sum-Free Partitions
│   ├── Sperner3D.lean                            # 26. Sperner's Lemma in 3D (Tetrahedral Parity)
│   ├── SpernerND.lean                            # 26. General n-Dimensional Sperner's Lemma & Pseudomanifolds
│   ├── SpernersLemma.lean                        # 8. Sperner's Lemma (1D & 2D) (Freek Wiedijk #57)
│   ├── SylvesterGallai.lean                      # 12. Sylvester–Gallai Theorem (Freek Wiedijk #98)
│   ├── SzemerediTrotter.lean                     # 29. Szemerédi–Trotter Theorem on Point-Line Incidences
│   ├── TuckersLemma.lean                         # 24. Tucker's Combinatorial Lemma
│   ├── TutteOneFactor.lean                       # 31. Tutte's 1-Factor Theorem & Tutte–Berge Formula
│   ├── TverbergsTheorem.lean                     # 16. Tverberg's Theorem (Master Interface)
│   └── TverbergsTheorem/                         # 16. Modular Tverberg Package
│       ├── Basis.lean                            #     - Auxiliary basis vectors & lifted affine coordinates
│       ├── Sarkaria.lean                         #     - Sarkaria algebraic reduction & Radon partition
│       ├── Dim1.lean                             #     - 1D Tverberg theorem via median & symmetric pairing
│       └── Colorful.lean                         #     - 1D Colorful Tverberg theorem (Bárány–Larman–Pach 1992)
├── palomar/                                      # Palomar Registry Benchmark Packages
│   ├── activate.ps1                              # Package staging automation
│   ├── audit.ps1                                 # Hermetic pre-flight audit runner
│   ├── batch_commit.ps1                          # Immutable Git SHA commit generator
│   ├── art_gallery_theorem/                      # Challenge.lean, Solution.lean, comparator.json, formalization.yaml
│   ├── becks_theorem/                            # ...
│   ├── bollobas_two_families/
│   ├── bondy_induced_subsets/
│   ├── cauchy_arm_lemma/
│   ├── colorful_caratheodory/                    # Verified suite: Carathéodory, Selection, Centerpoint
│   ├── colorful_helly/
│   ├── crossing_lemma/
│   ├── de_bruijn_erdos/
│   ├── desargues_theorem/
│   ├── descartes_rule_of_signs/
│   ├── dilworth_mirsky/
│   ├── elekes_sum_product/
│   ├── erdos_ko_rado/
│   ├── erdos_szekeres_convex/
│   ├── erdos_unit_distances/
│   ├── euler_polyhedron/
│   ├── frankl_wilson/
│   ├── friendship_theorem/
│   ├── friendship_windmill/
│   ├── graham_pollak/
│   ├── hall_marriage/
│   ├── kneser_lovasz/
│   ├── ore_dirac_hamiltonian/
│   ├── picks_theorem/
│   ├── radon_helly/
│   ├── schurs_theorem/
│   ├── sperner_3d/
│   ├── sperner_nd/
│   ├── sperners_lemma/
│   ├── sylvester_gallai/
│   ├── szemeredi_trotter/
│   ├── tuckers_lemma/
│   ├── tutte_one_factor/
│   └── tverbergs_theorem/                        # Verified suite: Tverberg, 1D Tverberg, 1D Colorful Tverberg
├── formalization.yaml                            # Root formalization metadata manifest
├── lake-manifest.json                            # Pinned Lake package dependencies
├── lakefile.toml                                 # Lake build system manifest
├── lean-toolchain                                # Pinned Lean 4 toolchain (leanprover/lean4:v4.34.0-rc1)
├── LICENSE                                       # CC0 1.0 Universal Public Domain Dedication
├── PALOMAR_CHECKLIST.md                          # Palomar pre-flight submission audit checklist
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

Individual modules and packages can be compiled independently:

```bash
lake build Formalization.ColorfulCaratheodory
lake build Formalization.TverbergsTheorem
lake build Formalization.ColorfulHelly
lake build Formalization.RadonHelly
lake build Formalization.SpernerND
lake build Formalization.ElekesSumProduct
lake build Formalization.SzemerediTrotter
lake build Formalization.ErdosUnitDistances
lake build Formalization.TutteOneFactor
lake build Formalization.FriendshipWindmill
lake build Formalization.FranklWilson
lake build Formalization.BecksTheorem
lake build Formalization
```

---

## License

This repository and all formalizations are dedicated to the public domain under the **[Creative Commons Zero v1.0 Universal (CC0 1.0)](LICENSE)** public domain dedication. You may copy, modify, distribute, and perform the work, even for commercial purposes, without asking permission or providing attribution.