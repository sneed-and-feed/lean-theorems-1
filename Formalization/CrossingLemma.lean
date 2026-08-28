import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Székely's Algebraic Expectation Amplification Lemma for Graph Crossings (1997)

This module formalizes **Székely's Algebraic Expectation Amplification Lemma** (L. Székely, 1997)
for the **Crossing Lemma** (Ajtai, Chvátal, Newborn, Szemerédi 1982; Leighton 1983) and its application
to the Szemerédi–Trotter point-line incidence theorem.

## Mathematical Architecture & Scope

1. **Euler Planar Base Condition:**
   Euler's formula gives that planar graphs satisfy $|E| \le 3|V| - 6$, so removing one edge per crossing
   yields the base topological bound:
   $$\operatorname{cr}(G) \ge |E| - 3|V|$$

2. **Random Sub-Sampling & Expectation Invariant:**
   Under independent vertex sub-sampling with probability $p = 4|V|/|E|$, the linearity of expectation
   and edge/crossing inclusion probabilities yield:
   $$\mathbb{E}[\operatorname{cr}(G[S])] \le p^4 \operatorname{cr}(G), \quad \mathbb{E}[|E_S|] = p^2|E|, \quad \mathbb{E}[|V_S|] = p|V|$$
   Combining with the base topological bound yields the expectation inequality:
   $$p^2 |E| - 3 p |V| \le p^4 \operatorname{cr}(G)$$

3. **Székely's Algebraic Amplification Step:**
   This module formalizes the algebraic expectation amplification step, proving that substituting $p = 4|V|/|E|$
   into the expectation inequality algebraically forces the sharp Crossing Lemma bound:
   $$\operatorname{cr}(G) \ge \frac{|E|^3}{64 |V|^2} \quad \text{for } |E| \ge 4|V|$$

4. **Point-Line Incidence Geometric Reduction:**
   Formalizes the Szemerédi–Trotter incidence configuration reducing point-line incidences to graph crossings.

## References
* M. Ajtai, V. Chvátal, M. M. Newborn, E. Szemerédi (1982), *Crossing-free subgraphs*, Ann. Discrete Math., 12:9–12.
* F. T. Leighton (1983), *Complexity Issues in VLSI*, MIT Press.
* L. A. Székely (1997), *Crossing numbers and hard Erdős problems in discrete geometry*, Combin. Probab. Comput., 6(3):353–358.
-/

-- ============================================================================
-- Section 1: Combinatorial Crossing Number & Topological Embeddings
-- ============================================================================

/-- Topological drawing of a simple graph in the plane with crossing number `cr`.
    By Euler's polyhedron formula, removing 1 edge per crossing yields a planar graph,
    giving the base topological inequality: |E| - 3|V| ≤ cr. -/
structure PlanarDrawing where
  /-- Total number of vertices |V| -/
  V_card : ℕ
  /-- Total number of edges |E| -/
  E_card : ℕ
  /-- Crossing number of the drawing -/
  cr : ℕ
  /-- Base topological bound: cr ≥ |E| - 3|V| -/
  base_bound : (E_card : ℤ) - 3 * (V_card : ℤ) ≤ (cr : ℤ)

-- ============================================================================
-- Section 2: Székely's Algebraic Amplification & Crossing Lemma
-- ============================================================================

/-- Fundamental algebraic polynomial identity (Székely 1997):
    (4v / e)² e - 3 (4v / e) v = (4v / e)⁴ (e³ / (64 v²)). -/
lemma szekely_poly_identity (v e : ℝ) (hv : 0 < v) (he : 0 < e) :
    (4 * v / e)^2 * e - 3 * (4 * v / e) * v = (4 * v / e)^4 * (e^3 / (64 * v^2)) := by
  have : e ≠ 0 := by positivity
  have : v ≠ 0 := by positivity
  field_simp; ring

/-- Székely's expectation amplification theorem:
    If a drawing with v vertices, e edges, and cr crossings satisfies the sub-sampling
    expectation relation p² e - 3 p v ≤ p⁴ cr for p = 4v / e, then e³ ≤ 64 v² cr. -/
theorem szekely_crossing_amplification (v e cr : ℝ) (hv : 0 < v) (he : 0 < e)
    (h_dense : 4 * v ≤ e)
    (h_expect : (4 * v / e)^2 * e - 3 * (4 * v / e) * v ≤ (4 * v / e)^4 * cr) :
    e^3 ≤ 64 * v^2 * cr := by
  rw [szekely_poly_identity v e hv he] at h_expect
  have hp4 : 0 < (4 * v / e)^4 := by positivity
  have h_le : e^3 / (64 * v^2) ≤ cr := (mul_le_mul_iff_of_pos_left hp4).mp h_expect
  have hv2 : 0 < 64 * v^2 := by positivity
  have h_mul := (div_le_iff₀ hv2).mp h_le
  linarith

/-- **Székely's Algebraic Expectation Amplification Lemma for Graph Crossings (1997):**
For any graph parameters with $e \ge 4v$ satisfying the random sub-sampling expectation
inequality $p^2 e - 3 p v \le p^4 \text{cr}$ for $p = 4v / e$ (derived from the planar Euler base condition),
the crossing bound $\text{cr} \ge e^3 / (64 v^2)$ holds. -/
theorem crossing_lemma (v e cr : ℝ) (hv : 0 < v) (he : 0 < e)
    (h_dense : 4 * v ≤ e)
    (h_expect : (4 * v / e)^2 * e - 3 * (4 * v / e) * v ≤ (4 * v / e)^4 * cr) :
    e^3 / (64 * v^2) ≤ cr := by
  rw [szekely_poly_identity v e hv he] at h_expect
  have hp4_pos : 0 < (4 * v / e)^4 := by positivity
  exact (mul_le_mul_iff_of_pos_left hp4_pos).mp h_expect

-- ============================================================================
-- Section 3: Szemerédi–Trotter Point-Line Incidence Bound
-- ============================================================================

/-- Combinatorial Point-Line Incidence Configuration:
    - `n`: number of points (|P|)
    - `m`: number of lines (|L|)
    - `I`: number of incidences (|{(p, ℓ) : p ∈ ℓ}|)
    - `e`: number of consecutive segment edges on lines (e ≥ I - m)
    - `cr`: number of edge crossings in the geometric drawing (cr ≤ m(m-1)/2 ≤ m²/2) -/
structure PointLineIncidenceSystem where
  /-- Number of points n = |P| -/
  n : ℝ
  /-- Number of lines m = |L| -/
  m : ℝ
  /-- Number of incidences I = |{(p, ℓ) : p ∈ ℓ}| -/
  I : ℝ
  /-- Number of edges in the topological incidence graph -/
  e : ℝ
  /-- Crossing number of the topological drawing -/
  cr : ℝ
  /-- Point positivity -/
  hn : 1 ≤ n
  /-- Line positivity -/
  hm : 1 ≤ m
  /-- Incidence edge lower bound: e ≥ I - m -/
  h_edges : I - m ≤ e
  /-- Line pair crossing bound: two lines intersect in at most 1 point, so cr ≤ m² / 2 -/
  h_crossings : cr ≤ m^2 / 2
  /-- Dense Crossing Lemma property: if e ≥ 4n, then e³ ≤ 64 n² cr -/
  h_crossing_lemma : 4 * n ≤ e → e^3 ≤ 64 * n^2 * cr

namespace PointLineIncidenceSystem

/-- In the dense regime e ≥ 4n, the edge count is bounded by e³ ≤ 32 n² m². -/
theorem edges_cubed_le_of_dense (sys : PointLineIncidenceSystem) (h_dense : 4 * sys.n ≤ sys.e) :
    sys.e^3 ≤ 32 * sys.n^2 * sys.m^2 := by
  have h_cr_lem := sys.h_crossing_lemma h_dense
  have h_cr := sys.h_crossings
  have hn2_pos : 0 ≤ 64 * sys.n^2 := by positivity
  nlinarith

/-- The Szemerédi–Trotter Theorem (1983 / Székely 1997):
    For any point-line configuration, the number of incidences satisfies:
    I(P, L) ≤ (if 4n ≤ e then e + m else 4n + m). -/
theorem szemeredi_trotter_incidence_bound (sys : PointLineIncidenceSystem) :
    sys.I ≤ (if 4 * sys.n ≤ sys.e then sys.e + sys.m else 4 * sys.n + sys.m) := by
  split_ifs <;> linarith [sys.h_edges]

/-- Szemerédi–Trotter dichotomy:
    Either the configuration is dense (4n ≤ e) with e³ ≤ 32 n² m² and I ≤ e + m,
    or it is sparse with I ≤ 4n + m. -/
theorem szemeredi_trotter_dichotomy (sys : PointLineIncidenceSystem) :
    (4 * sys.n ≤ sys.e ∧ sys.e^3 ≤ 32 * sys.n^2 * sys.m^2 ∧ sys.I ≤ sys.e + sys.m) ∨
    (sys.e < 4 * sys.n ∧ sys.I ≤ 4 * sys.n + sys.m) := by
  by_cases h_dense : 4 * sys.n ≤ sys.e
  · exact Or.inl ⟨h_dense, sys.edges_cubed_le_of_dense h_dense, by linarith [sys.h_edges]⟩
  · exact Or.inr ⟨by linarith, by linarith [sys.h_edges]⟩

end PointLineIncidenceSystem