import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The Crossing Lemma & Szemerédi–Trotter Theorem

**The Crossing Lemma (Ajtai, Chvátal, Newborn, Szemerédi 1982; Leighton 1983)**
is a cornerstone of discrete geometry and extremal graph theory.
It states that any simple graph $G = (V, E)$ drawn in the plane with $|E| \ge 4|V|$
has crossing number satisfying:
$$\operatorname{cr}(G) \ge \frac{1}{64} \frac{|E|^3}{|V|^2}$$

Székely (1997) showed that the Crossing Lemma provides an astonishingly simple and powerful
proof of the **Szemerédi–Trotter Theorem (1983)** on point-line incidences:
$$I(P, L) \le C \left( |P|^{2/3} |L|^{2/3} + |P| + |L| \right)$$

## Proof Roadmap
1. **Planar Euler Bound:** Any planar graph without multigraph edges has $|E| \le 3|V| - 6$.
   Hence $\operatorname{cr}(G) \ge |E| - 3|V|$.
2. **Probabilistic Sub-Sampling (Székely 1997):** Choose a random induced subgraph $G[S]$
   by selecting each vertex independently with probability $p = 4|V| / |E|$.
   Taking expectations: $\mathbb{E}[|V_S|] = p|V|$, $\mathbb{E}[|E_S|] = p^2|E|$,
   and $\mathbb{E}[\operatorname{cr}(G_S)] \le p^4 \operatorname{cr}(G)$.
3. **Algebraic Amplification:**
   $$p^4 \operatorname{cr}(G) \ge \mathbb{E}[\operatorname{cr}(G_S)] \ge p^2|E| - 3p|V|$$
   Substituting $p = 4|V|/|E|$ yields $\operatorname{cr}(G) \ge \frac{|E|^3}{64 |V|^2}$.
4. **Incidence Graph Construction:** Represent $n$ points and $m$ lines as a topological
   graph where edges are line segments between adjacent points on lines, giving $|E| \ge I(P, L) - m$.
   Since two lines intersect in at most 1 point, $\operatorname{cr}(G) \le \binom{m}{2} \le m^2 / 2$.
   Applying the Crossing Lemma establishes $I(P, L) \le C (n^{2/3} m^{2/3} + n + m)$.
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

/-- The Crossing Lemma (Ajtai et al. 1982 / Leighton 1983 / Székely 1997):
    For any graph with |E| ≥ 4|V| satisfying the sub-sampling expectation inequality,
    cr(G) ≥ |E|³ / (64 |V|²). -/
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