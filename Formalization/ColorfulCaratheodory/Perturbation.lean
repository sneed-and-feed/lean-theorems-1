import Formalization.ColorfulCaratheodory.Basic
import Formalization.ColorfulCaratheodory.Separation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open BigOperators Finset

noncomputable section

namespace ColorfulCaratheodory

variable {d : ℕ}

/-- Given $q, p, s$ with $\|q - p\|^2 > 0$ and $\langle q - p, s - p \rangle \le 0$,
there exists $\varepsilon \in (0, 1)$ such that the interpolated point
$y = (1 - \varepsilon) q + \varepsilon s$ satisfies $\|y - p\|^2 < \|q - p\|^2$. -/
lemma exists_strictly_decreasing_segment_point (p q s : Fin d → ℝ)
    (hv : 0 < euclideanSq (q - p)) (hdot : dotProd (q - p) (s - p) ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      euclideanSq ((1 - ε) • q + ε • s - p) < euclideanSq (q - p) := by
  let v := q - p; let u := s - p
  let Ev := euclideanSq v; let Eu := euclideanSq u
  have hdenom : 0 < Ev + Eu + 1 := by linarith [euclideanSq_nonneg u]
  let ε := Ev / (Ev + Eu + 1)
  have hε : 0 < ε := div_pos hv hdenom
  have hε1 : ε < 1 := (div_lt_one hdenom).mpr (by linarith [euclideanSq_nonneg u])
  refine ⟨ε, hε, hε1, ?_⟩
  have h_comb : (1 - ε) • q + ε • s - p = (1 - ε) • v + ε • u := by
    ext i; simp only [v, u, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h_comb, euclideanSq_smul_add_smul (1 - ε) ε v u]
  have h_frac : ε * (Ev + Eu) < Ev := by
    dsimp [ε]; rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom]; nlinarith
  have h_bound : (1 - ε) ^ 2 * Ev + 2 * (1 - ε) * ε * dotProd v u + ε ^ 2 * Eu ≤ (1 - ε) ^ 2 * Ev + ε ^ 2 * Eu := by
    have : 2 * (1 - ε) * ε * dotProd v u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by nlinarith) hdot
    linarith
  have h_quad : (1 - ε) ^ 2 * Ev + ε ^ 2 * Eu < Ev := by
    have : (1 - ε) ^ 2 * Ev + ε ^ 2 * Eu - Ev = ε * (ε * (Ev + Eu) - Ev) - ε * Ev := by ring
    have : ε * (ε * (Ev + Eu) - Ev) < 0 := mul_neg_of_pos_of_neg hε (by linarith [h_frac])
    linarith [mul_pos hε hv]
  exact lt_of_le_of_lt h_bound h_quad

/-- Point-existence form of the segment distance strictly decreasing lemma. -/
lemma exists_closer_point_on_segment (p q s : Fin d → ℝ)
    (hv : q ≠ p) (hdot : dotProd (q - p) (s - p) ≤ 0) :
    ∃ y : Fin d → ℝ, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      y = (1 - ε) • q + ε • s ∧ euclideanSq (y - p) < euclideanSq (q - p) := by
  have hpos : 0 < euclideanSq (q - p) := (euclideanSq_pos_iff _).mpr (sub_ne_zero.mpr hv)
  obtain ⟨ε, hε_pos, hε_lt1, hlt⟩ := exists_strictly_decreasing_segment_point p q s hpos hdot
  exact ⟨_, ε, hε_pos, hε_lt1, rfl, hlt⟩

/-- Convex hull membership preservation under segment interpolation. -/
lemma segment_mem_convexHull_insert (s : Fin d → ℝ) (T : Set (Fin d → ℝ)) (q : Fin d → ℝ)
    (hq : q ∈ convexHull ℝ T) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) • q + ε • s ∈ convexHull ℝ (insert s T) :=
  convex_convexHull ℝ _ (convexHull_mono (Set.subset_insert s T) hq)
    (subset_convexHull ℝ _ (Set.mem_insert s T)) (by linarith) hε0 (by ring)

end ColorfulCaratheodory
