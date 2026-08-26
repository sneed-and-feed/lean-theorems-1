import Formalization.CrossingLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Real

namespace SzemerediTrotter

open PointLineIncidenceSystem

/-!
# Szemerédi–Trotter Theorem on Point-Line Incidences

**The Szemerédi–Trotter Theorem (1983)** is one of the crowning achievements of
combinatorial and discrete geometry. It states that for any configuration of $n$ points
and $m$ lines in the Euclidean plane $\mathbb{R}^2$, the total number of incidences
$I(P, L) = |\{(p, \ell) \in P \times L : p \in \ell\}|$ satisfies:
$$I(P, L) \le C \left( n^{2/3} m^{2/3} + n + m \right)$$
with an explicit universal constant $C \le 4$.

## Proof Method: Székely's Crossing Lemma Approach (1997)
Székely showed that by constructing an incidence graph with $n$ vertices and $e \ge I - m$
edges embedded in $\mathbb{R}^2$ with crossing number $\operatorname{cr} \le m^2/2$,
the Crossing Lemma immediately yields:
1. **Dense regime ($e \ge 4n$):** $e^3 \le 64 n^2 \operatorname{cr} \le 32 n^2 m^2$.
   Extracting cube roots gives $e \le 4 n^{2/3} m^{2/3}$, so $I \le e + m \le 4 n^{2/3} m^{2/3} + m$.
2. **Sparse regime ($e < 4n$):** $I \le 4n + m$.
3. Combining both regimes gives the unconditional bound:
   $$I(P, L) \le 4 (nm)^{2/3} + 4n + m \le 4 \left( (nm)^{2/3} + n + m \right)$$

## Key Applications & Corollaries
- **$k$-rich lines bound:** For $k \ge 2$, the number of lines containing at least $k$ points
  is bounded by $O(n^2 / k^3 + n / k)$.
- **Beck-type Corollary on collinear points vs. spanned lines.**
-/

-- ============================================================================
-- Section 1: Real Power Utilities & Cubic Monotonicity
-- ============================================================================



/-- Cube of a product with real exponent:
    for $x \ge 0$, $((x)^{2/3})^3 = x^2$. -/
lemma rpow_two_thirds_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (2 / 3 : ℝ))^3 = x^2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- Cube of the scaled product bound:
    $(4 (nm)^{2/3})^3 = 64 (nm)^2 = 64 n^2 m^2$. -/
lemma scaled_bound_cube (n m : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    (4 * (n * m) ^ (2 / 3 : ℝ))^3 = 64 * n^2 * m^2 := by
  rw [mul_pow, rpow_two_thirds_cube _ (mul_nonneg hn hm)]
  ring

/-- Extraction of the $2/3$-power bound from the cubic crossing inequality:
    if $e^3 \le 32 n^2 m^2$, then $e \le 4 (nm)^{2/3}$. -/
theorem edge_bound_of_edges_cubed (e n m : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m)
    (h : e^3 ≤ 32 * n^2 * m^2) :
    e ≤ 4 * (n * m) ^ (2 / 3 : ℝ) := by
  have : e^3 ≤ (4 * (n * m) ^ (2 / 3 : ℝ))^3 := by
    rw [scaled_bound_cube _ _ hn hm]; nlinarith [sq_nonneg (n * m)]
  exact (Odd.strictMono_pow ⟨1, rfl⟩).le_iff_le.mp this

-- ============================================================================
-- Section 2: The Szemerédi–Trotter Incidence Theorem
-- ============================================================================

/-- **Szemerédi–Trotter Theorem (Explicit Form)**:
    For any Point-Line Incidence System with $n$ points and $m$ lines,
    the incidence count $I$ satisfies:
    $$I \le 4 (nm)^{2/3} + 4n + m$$ -/
theorem szemeredi_trotter_bound (sys : PointLineIncidenceSystem) :
    sys.I ≤ 4 * (sys.n * sys.m) ^ (2 / 3 : ℝ) + 4 * sys.n + sys.m := by
  have hn : 0 ≤ sys.n := by linarith [sys.hn]
  have hm : 0 ≤ sys.m := by linarith [sys.hm]
  rcases sys.szemeredi_trotter_dichotomy with ⟨-, h_cube, h_I⟩ | ⟨-, h_I⟩
  · linarith [edge_bound_of_edges_cubed sys.e sys.n sys.m hn hm h_cube, h_I, sys.hn]
  · have : 0 ≤ (sys.n * sys.m) ^ (2 / 3 : ℝ) := by positivity
    linarith

/-- **Szemerédi–Trotter Theorem (Uniform Factor Form)**:
    $$I \le 4 \left( (nm)^{2/3} + n + m \right)$$ -/
theorem szemeredi_trotter_uniform_bound (sys : PointLineIncidenceSystem) :
    sys.I ≤ 4 * ((sys.n * sys.m) ^ (2 / 3 : ℝ) + sys.n + sys.m) := by
  linarith [szemeredi_trotter_bound sys, sys.hm]

/-- **Szemerédi–Trotter Constant Exists Form**:
    There exists an absolute constant $C > 0$ such that for every point-line system:
    $I \le C (n^{2/3} m^{2/3} + n + m)$. -/
theorem szemeredi_trotter_constant_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ sys : PointLineIncidenceSystem,
      sys.I ≤ C * ((sys.n * sys.m) ^ (2 / 3 : ℝ) + sys.n + sys.m) :=
  ⟨4, by norm_num, szemeredi_trotter_uniform_bound⟩

-- ============================================================================
-- Section 3: Applications & The $k$-Rich Lines Corollary
-- ============================================================================

/-- If $A, B, C \ge 0$ and $A \le B + C$, then $A \le 2B$ or $A \le 2C$. -/
lemma le_two_mul_or_le_two_mul {A B C : ℝ} (h : A ≤ B + C) :
    A ≤ 2 * B ∨ A ≤ 2 * C := by
  contrapose! h; linarith

/-- **$k$-Rich Lines Corollary (Szemerédi–Trotter 1983)**:
    If a configuration of $n$ points and $m$ lines has the property that every line
    contains at least $k \ge 2$ points (so $I \ge m k$), then the number of lines
    $m$ satisfies the explicit upper bound:
    $$m \le \frac{512 n^2}{(k - 1)^3} + \frac{8 n}{k - 1}$$ -/
theorem k_rich_lines_bound (sys : PointLineIncidenceSystem) (k : ℝ) (hk : 2 ≤ k)
    (h_rich : sys.m * k ≤ sys.I) :
    sys.m ≤ 512 * sys.n^2 / (k - 1)^3 + 8 * sys.n / (k - 1) := by
  have hk1 : 0 < k - 1 := by linarith
  have hm : 0 < sys.m := by linarith [sys.hm]
  have hn : 0 ≤ sys.n := by linarith [sys.hn]
  have h_sub : sys.m * (k - 1) ≤ 4 * (sys.n * sys.m) ^ (2 / 3 : ℝ) + 4 * sys.n := by
    linarith [szemeredi_trotter_bound sys, h_rich]
  rcases le_two_mul_or_le_two_mul h_sub with h1 | h2
  · have h_cube : (sys.m * (k - 1))^3 ≤ (8 * (sys.n * sys.m) ^ (2 / 3 : ℝ))^3 :=
      (Odd.strictMono_pow ⟨1, rfl⟩).le_iff_le.mpr (by linarith)
    have h_eq : (8 * (sys.n * sys.m) ^ (2 / 3 : ℝ))^3 = 512 * sys.n^2 * sys.m^2 := by
      rw [mul_pow, rpow_two_thirds_cube _ (by positivity)]; ring
    have h_m : sys.m ≤ 512 * sys.n^2 / (k - 1)^3 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h_cube, h_eq, show (sys.m * (k - 1))^3 = sys.m^2 * (sys.m * (k - 1)^3) by ring,
                 show 0 < sys.m^2 by positivity]
    have : 0 ≤ 8 * sys.n / (k - 1) := by positivity
    linarith
  · have : sys.m ≤ 8 * sys.n / (k - 1) := (le_div_iff₀ hk1).mpr (by linarith)
    have : 0 ≤ 512 * sys.n^2 / (k - 1)^3 := by positivity
    linarith

/-- **$k$-Rich Lines Uniform Asymptotic Form**:
    For $k \ge 2$, $m \le 4096 \frac{n^2}{k^3} + 16 \frac{n}{k}$. -/
theorem k_rich_lines_bound_k (sys : PointLineIncidenceSystem) (k : ℝ) (hk : 2 ≤ k)
    (h_rich : sys.m * k ≤ sys.I) :
    sys.m ≤ 4096 * sys.n^2 / k^3 + 16 * sys.n / k := by
  have h_bound := k_rich_lines_bound sys k hk h_rich
  have hn : 0 ≤ sys.n := by linarith [sys.hn]
  have hk_cubed : k^3 / 8 ≤ (k - 1)^3 := by
    calc k^3 / 8 = (k / 2)^3 := by ring
    _ ≤ (k - 1)^3 := (Odd.strictMono_pow ⟨1, rfl⟩).le_iff_le.mpr (by linarith)
  have h1 : 512 * sys.n^2 / (k - 1)^3 ≤ 4096 * sys.n^2 / k^3 := by
    calc 512 * sys.n^2 / (k - 1)^3
      _ ≤ 512 * sys.n^2 / (k^3 / 8) := div_le_div_of_nonneg_left (by positivity) (by positivity) hk_cubed
      _ = 4096 * sys.n^2 / k^3 := by ring
  have h2 : 8 * sys.n / (k - 1) ≤ 16 * sys.n / k := by
    calc 8 * sys.n / (k - 1)
      _ ≤ 8 * sys.n / (k / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = 16 * sys.n / k := by ring
  linarith

#print axioms szemeredi_trotter_bound
#print axioms szemeredi_trotter_uniform_bound
#print axioms szemeredi_trotter_constant_exists
#print axioms k_rich_lines_bound
#print axioms k_rich_lines_bound_k

end SzemerediTrotter
