import Formalization.ColorfulCaratheodory.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open BigOperators Finset

noncomputable section

namespace ColorfulCaratheodory

variable {d : ℕ}

lemma sum_smul_sub_eq_zero {S : Finset (Fin d → ℝ)} {w : (Fin d → ℝ) → ℝ} {p : Fin d → ℝ}
    (hw_sum : ∑ y ∈ S, w y = 1) (hp : ∑ y ∈ S, w y • y = p) :
    ∑ y ∈ S, w y • (y - p) = 0 := by
  simp_rw [smul_sub, sum_sub_distrib, ← sum_smul, hp, hw_sum, one_smul, sub_self]

/-- If $p \in \operatorname{conv}(S)$ for a finite set $S$, and $\langle v, s - p \rangle > 0$
for all $s \in S$, we obtain a contradiction $0 > 0$. -/
lemma dotProd_sub_pos_contradiction {S : Finset (Fin d → ℝ)} {p : Fin d → ℝ}
    (hp : p ∈ convexHull ℝ (S : Set (Fin d → ℝ))) (v : Fin d → ℝ)
    (h_pos : ∀ s ∈ S, 0 < dotProd v (s - p)) : False := by
  obtain ⟨w, hw_nonneg, hw_sum, hp_cm⟩ := Finset.mem_convexHull.mp hp
  have hp_eq : ∑ y ∈ S, w y • y = p := by dsimp [centerMass] at hp_cm; rwa [hw_sum, inv_one, one_smul] at hp_cm
  have h_zero : ∑ y ∈ S, w y * dotProd v (y - p) = 0 := by
    rw [← dotProd_sum_smul_right, sum_smul_sub_eq_zero hw_sum hp_eq, dotProd_zero_right]
  have ⟨s0, hs0, hw_s0⟩ : ∃ s ∈ S, 0 < w s := by
    by_contra! h_le
    exact ne_of_gt (by linarith : 0 < ∑ s ∈ S, w s) (sum_eq_zero fun s hs ↦ le_antisymm (h_le s hs) (hw_nonneg s hs))
  have h_pos_sum : 0 < ∑ y ∈ S, w y * dotProd v (y - p) :=
    (mul_pos hw_s0 (h_pos s0 hs0)).trans_le
      (single_le_sum (fun y hy ↦ mul_nonneg (hw_nonneg y hy) (le_of_lt (h_pos y hy))) hs0)
  linarith

/-- Linear functional separation on convex hulls: If $p \in \operatorname{conv}(S)$ for a finite set $S$,
there exists $s \in S$ satisfying $\langle v, s - p \rangle \le 0$. -/
lemma exists_nonpos_dotProd_of_mem_convexHull {S : Finset (Fin d → ℝ)} {p : Fin d → ℝ}
    (hp : p ∈ convexHull ℝ (S : Set (Fin d → ℝ))) (v : Fin d → ℝ) :
    ∃ s ∈ S, dotProd v (s - p) ≤ 0 := by
  by_contra! h; exact dotProd_sub_pos_contradiction hp v h

/-- Alias for `exists_nonpos_dotProd_of_mem_convexHull`. -/
lemma exists_dotProd_sub_le_zero {S : Finset (Fin d → ℝ)} {p : Fin d → ℝ}
    (hp : p ∈ convexHull ℝ (S : Set (Fin d → ℝ))) (v : Fin d → ℝ) :
    ∃ s ∈ S, dotProd v (s - p) ≤ 0 :=
  exists_nonpos_dotProd_of_mem_convexHull hp v

end ColorfulCaratheodory
