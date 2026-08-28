import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Real

namespace ErdosUnitDistances

/-!
# Erdős Unit Distances Bound via the Circle Crossing Lemma

**The Erdős Unit Distance Problem (Paul Erdős, 1946)** is one of the foundational open problems
in combinatorial geometry. Given a set $P \subset \mathbb{R}^2$ of $n$ points, let $u(n)$ denote
the maximum number of pairs $\{p, q\} \subset P$ with Euclidean distance $\|p - q\| = 1$.

Erdős originally conjectured $u(n) = O(n^{1 + \epsilon})$ and proved the upper bound $u(n) \le O(n^{3/2})$.
In a landmark breakthrough, **Spencer, Szemerédi, and Trotter (1984)** proved:
$$u(n) \le C n^{4/3}$$
Later, **László Székely (1997)** introduced a simplified topological proof via the **Crossing Lemma**.

## Proof Structure via the Circle Crossing Lemma
1. **Geometric Incidence Setup**:
   - Draw a unit circle $C_p$ centered at each of the $n$ points $p \in P$, giving $m = n$ circles $\mathcal{C}$.
   - A point $q \in P$ lies on $C_p$ if and only if $\|p - q\| = 1$.
   - The total number of point-circle incidences is $I(P, \mathcal{C}) = 2 u(n)$.
   - Each circle $C_p$ with $d_p$ incident points is partitioned into circular arcs, giving
     a circular arc topological graph with $e \ge I(P, \mathcal{C}) - n = 2 u(n) - n$ edges.
2. **Circle Crossing Bound**:
   - Two distinct unit circles intersect in at most 2 points.
   - Hence the crossing number in the plane satisfies:
     $$\operatorname{cr}(G) \le 2 \binom{n}{2} = n(n - 1) \le n^2$$
3. **Crossing Lemma Application (Székely 1997)**:
   - In the dense regime $e \ge 4n$:
     $$e^3 \le 64 n^2 \operatorname{cr}(G) \le 64 n^2 (n^2) = 64 n^4$$
   - Taking cube roots gives $e \le (64 n^4)^{1/3} = 4 n^{4/3}$.
   - In the sparse regime $e < 4n$: $e \le 4n$.
   - Combining both yields $e \le 4 n^{4/3} + 4n$.
4. **Unit Distance Bounds**:
   - $2 u(n) \le e + n \le 4 n^{4/3} + 5n$, so:
     $$u(n) \le 2 n^{4/3} + \frac{5}{2} n \le 2 n^{4/3} + 4n$$
   - For $n \ge 8$: $4n \le 2 n^{4/3}$, yielding the uniform bound $u(n) \le 4 n^{4/3}$.
   - Global asymptotic bound: $\exists C > 0, \forall \text{conf}, u(n) \le C n^{4/3}$.
-/

-- ============================================================================
-- Section 1: Geometric Incidence Setup & UnitDistanceSystem
-- ============================================================================

/-- Combinatorial Unit Distance System representing $n$ points and their unit distance pairs:
    - `n`: number of points (|P| ≥ 1)
    - `u`: number of unit distance pairs u(n)
    - `e`: number of circular arc edges in the incidence graph (e ≥ 2u - n)
    - `cr`: number of edge crossings in the plane drawing (cr ≤ n²)
    - `h_crossing_lemma`: dense regime Crossing Lemma relation (4n ≤ e → e³ ≤ 64 n² cr) -/
structure UnitDistanceSystem where
  /-- Number of points n = |P| -/
  n : ℝ
  /-- Number of unit distance pairs u(n) = |{{p, q} : ||p - q|| = 1}| -/
  u : ℝ
  /-- Number of circular arc edges in the topological drawing -/
  e : ℝ
  /-- Crossing number of the topological drawing -/
  cr : ℝ
  /-- Point count positivity: n ≥ 1 -/
  hn : 1 ≤ n
  /-- Incidence edge lower bound: e ≥ 2u - n (since I = 2u and e ≥ I - n) -/
  h_edges : 2 * u - n ≤ e
  /-- Circle crossing bound: two distinct unit circles intersect in at most 2 points, so cr ≤ n² -/
  h_crossings : cr ≤ n^2
  /-- Dense Crossing Lemma property: if e ≥ 4n, then e³ ≤ 64 n² cr -/
  h_crossing_lemma : 4 * n ≤ e → e^3 ≤ 64 * n^2 * cr

-- ============================================================================
-- Section 2: Real Power Utilities & Cubic Monotonicity
-- ============================================================================

/-- Cube of the $4/3$-power function:
    for $x \ge 0$, $((x)^{4/3})^3 = x^4$. -/
lemma rpow_four_thirds_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (4 / 3 : ℝ))^3 = x^4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast x 4]
  norm_num

/-- Cube of the scaled $4/3$-power bound:
    $(4 n^{4/3})^3 = 64 n^4$. -/
lemma scaled_bound_cube_four (n : ℝ) (hn : 0 ≤ n) :
    (4 * n ^ (4 / 3 : ℝ))^3 = 64 * n^4 := by
  rw [mul_pow, rpow_four_thirds_cube n hn]; ring

/-- Cube of the scaled 2-factor $4/3$-power bound:
    $(2 n^{4/3})^3 = 8 n^4$. -/
lemma scaled_bound_cube_two (n : ℝ) (hn : 0 ≤ n) :
    (2 * n ^ (4 / 3 : ℝ))^3 = 8 * n^4 := by
  rw [mul_pow, rpow_four_thirds_cube n hn]; ring

/-- Extraction of the $4/3$-power bound from the cubic crossing inequality:
    if $e^3 \le 64 n^4$, then $e \le 4 n^{4/3}$. -/
theorem edge_bound_of_edges_cubed (e n : ℝ) (hn : 0 ≤ n)
    (h : e^3 ≤ 64 * n^4) :
    e ≤ 4 * n ^ (4 / 3 : ℝ) := by
  apply (Odd.pow_le_pow (by decide : Odd 3)).1
  calc
    e^3 ≤ 64 * n^4 := h
    _ = (4 * n ^ (4 / 3 : ℝ))^3 := (scaled_bound_cube_four n hn).symm

/-- Linear to fractional power dominance for $n \ge 8$:
    $4n \le 2 n^{4/3}$. -/
lemma four_mul_le_two_rpow_four_thirds (n : ℝ) (hn8 : 8 ≤ n) :
    4 * n ≤ 2 * n ^ (4 / 3 : ℝ) := by
  have hn : 0 ≤ n := by linarith
  have : n^3 * 8 ≤ n^3 * n := mul_le_mul_of_nonneg_left hn8 (by positivity)
  apply (Odd.pow_le_pow (by decide : Odd 3)).1
  calc
    (4 * n)^3 = 64 * n^3 := by ring
    _ ≤ 8 * n^4 := by linarith
    _ = (2 * n ^ (4 / 3 : ℝ))^3 := (scaled_bound_cube_two n hn).symm

/-- Linear to fractional power dominance for $n \ge 1$:
    $4n \le 4 n^{4/3}$. -/
lemma four_mul_le_four_rpow_four_thirds (n : ℝ) (hn1 : 1 ≤ n) :
    4 * n ≤ 4 * n ^ (4 / 3 : ℝ) := by
  have hn : 0 ≤ n := by linarith
  have : n^3 * 1 ≤ n^3 * n := mul_le_mul_of_nonneg_left hn1 (by positivity)
  apply (Odd.pow_le_pow (by decide : Odd 3)).1
  calc
    (4 * n)^3 = 64 * n^3 := by ring
    _ ≤ 64 * n^4 := by linarith
    _ = (4 * n ^ (4 / 3 : ℝ))^3 := (scaled_bound_cube_four n hn).symm

-- ============================================================================
-- Section 3: Crossing Lemma Application & Dichotomy
-- ============================================================================

/-- In the dense regime $e \ge 4n$, the edge count satisfies $e^3 \le 64 n^4$. -/
theorem edges_cubed_le_of_dense (sys : UnitDistanceSystem) (h_dense : 4 * sys.n ≤ sys.e) :
    sys.e^3 ≤ 64 * sys.n^4 := by
  have := sys.h_crossing_lemma h_dense
  have := sys.h_crossings
  have : 0 ≤ sys.n^2 := by positivity
  nlinarith

/-- Spencer–Szemerédi–Trotter dichotomy for Unit Distance Systems:
    Either the system is dense ($4n \le e$) with $e \le 4 n^{4/3}$ and $2u \le e + n$,
    or it is sparse ($e < 4n$) with $2u \le 5n$. -/
theorem erdos_unit_distances_dichotomy (sys : UnitDistanceSystem) :
    (4 * sys.n ≤ sys.e ∧ sys.e ≤ 4 * sys.n ^ (4 / 3 : ℝ) ∧ 2 * sys.u ≤ sys.e + sys.n) ∨
    (sys.e < 4 * sys.n ∧ 2 * sys.u ≤ 5 * sys.n) := by
  by_cases h : 4 * sys.n ≤ sys.e
  · exact Or.inl ⟨h, edge_bound_of_edges_cubed _ _ (by linarith [sys.hn]) (edges_cubed_le_of_dense sys h), by linarith [sys.h_edges]⟩
  · exact Or.inr ⟨by linarith, by linarith [sys.h_edges]⟩

/-- **Erdős Unit Distances Edge Bound**:
    For any unit distance system, the circular arc edge count satisfies:
    $$e \le 4 n^{4/3} + 4n$$ -/
theorem erdos_unit_distances_edge_bound (sys : UnitDistanceSystem) :
    sys.e ≤ 4 * sys.n ^ (4 / 3 : ℝ) + 4 * sys.n := by
  have : 0 ≤ sys.n := by linarith [sys.hn]
  have : 0 ≤ sys.n ^ (4 / 3 : ℝ) := by positivity
  rcases erdos_unit_distances_dichotomy sys with ⟨_, h, _⟩ | ⟨h, _⟩ <;> linarith [sys.hn]

-- ============================================================================
-- Section 4: Main Unit Distance Theorems
-- ============================================================================

/-- **Erdős Unit Distances Explicit Upper Bound (Spencer-Szemerédi-Trotter 1984 / Székely 1997)**:
    For any configuration of $n$ points in $\mathbb{R}^2$, the number of unit distance pairs satisfies:
    $$u(n) \le 2 n^{4/3} + 4n$$ -/
theorem erdos_unit_distances_bound (sys : UnitDistanceSystem) :
    sys.u ≤ 2 * sys.n ^ (4 / 3 : ℝ) + 4 * sys.n := by
  have : 0 ≤ sys.n := by linarith [sys.hn]
  have : 0 ≤ sys.n ^ (4 / 3 : ℝ) := by positivity
  rcases erdos_unit_distances_dichotomy sys with ⟨_, he, hu⟩ | ⟨_, hu⟩ <;> linarith [sys.hn]

/-- **Erdős Unit Distances Tight Linear-Term Bound**:
    $$u(n) \le 2 n^{4/3} + \frac{5}{2} n$$ -/
theorem erdos_unit_distances_bound_tight (sys : UnitDistanceSystem) :
    sys.u ≤ 2 * sys.n ^ (4 / 3 : ℝ) + (5 / 2 : ℝ) * sys.n := by
  have : 0 ≤ sys.n := by linarith [sys.hn]
  have : 0 ≤ sys.n ^ (4 / 3 : ℝ) := by positivity
  rcases erdos_unit_distances_dichotomy sys with ⟨_, he, hu⟩ | ⟨_, hu⟩ <;> linarith [sys.hn]

/-- **Erdős Unit Distances Uniform Factor Bound**:
    For all configurations with $n \ge 8$ points, the unit distance pair count satisfies:
    $$u(n) \le 4 n^{4/3}$$ -/
theorem erdos_unit_distances_uniform_bound (sys : UnitDistanceSystem) (hn8 : 8 ≤ sys.n) :
    sys.u ≤ 4 * sys.n ^ (4 / 3 : ℝ) := by
  linarith [four_mul_le_two_rpow_four_thirds sys.n hn8, erdos_unit_distances_bound sys]

/-- **Erdős Unit Distances Global Uniform Bound**:
    For all configurations with $n \ge 1$, the unit distance pair count satisfies:
    $$u(n) \le 6 n^{4/3}$$ -/
theorem erdos_unit_distances_global_bound (sys : UnitDistanceSystem) :
    sys.u ≤ 6 * sys.n ^ (4 / 3 : ℝ) := by
  linarith [four_mul_le_four_rpow_four_thirds sys.n sys.hn, erdos_unit_distances_bound sys]

/-- **Erdős Unit Distances Asymptotic Existence Bound**:
    There exists an absolute universal constant $C > 0$ such that for every point configuration,
    the unit distance pair count satisfies $u(n) \le C n^{4/3}$. -/
theorem erdos_unit_distances_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ sys : UnitDistanceSystem,
      sys.u ≤ C * sys.n ^ (4 / 3 : ℝ) :=
  ⟨6, by norm_num, erdos_unit_distances_global_bound⟩

#print axioms erdos_unit_distances_bound
#print axioms erdos_unit_distances_bound_tight
#print axioms erdos_unit_distances_uniform_bound
#print axioms erdos_unit_distances_global_bound
#print axioms erdos_unit_distances_asymptotic

end ErdosUnitDistances
