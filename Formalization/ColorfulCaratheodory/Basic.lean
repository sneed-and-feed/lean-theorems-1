import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open BigOperators Finset

noncomputable section

namespace ColorfulCaratheodory

variable {d : ℕ}

/-- Standard Euclidean inner product on `Fin d → ℝ`. -/
def dotProd (x y : Fin d → ℝ) : ℝ := ∑ i, x i * y i

/-- Squared Euclidean norm on `Fin d → ℝ`. -/
def euclideanSq (x : Fin d → ℝ) : ℝ := dotProd x x

@[simp]
lemma dotProd_comm (x y : Fin d → ℝ) : dotProd x y = dotProd y x := by
  simp only [dotProd, mul_comm]

@[simp] lemma dotProd_zero_left (x : Fin d → ℝ) : dotProd 0 x = 0 := by simp [dotProd]
@[simp] lemma dotProd_zero_right (x : Fin d → ℝ) : dotProd x 0 = 0 := by simp [dotProd]

lemma dotProd_add_left (x y z : Fin d → ℝ) : dotProd (x + y) z = dotProd x z + dotProd y z := by
  simp only [dotProd, Pi.add_apply, add_mul, sum_add_distrib]

lemma dotProd_add_right (x y z : Fin d → ℝ) : dotProd x (y + z) = dotProd x y + dotProd x z := by
  simp only [dotProd, Pi.add_apply, mul_add, sum_add_distrib]

lemma dotProd_neg_left (x y : Fin d → ℝ) : dotProd (-x) y = -dotProd x y := by
  simp only [dotProd, Pi.neg_apply, neg_mul, ← sum_neg_distrib]

lemma dotProd_neg_right (x y : Fin d → ℝ) : dotProd x (-y) = -dotProd x y := by
  simp only [dotProd, Pi.neg_apply, mul_neg, ← sum_neg_distrib]

lemma dotProd_sub_left (x y z : Fin d → ℝ) : dotProd (x - y) z = dotProd x z - dotProd y z := by
  simp only [sub_eq_add_neg, dotProd_add_left, dotProd_neg_left]

lemma dotProd_sub_right (x y z : Fin d → ℝ) : dotProd x (y - z) = dotProd x y - dotProd x z := by
  simp only [sub_eq_add_neg, dotProd_add_right, dotProd_neg_right]

lemma dotProd_smul_left (c : ℝ) (x y : Fin d → ℝ) : dotProd (c • x) y = c * dotProd x y := by
  simp only [dotProd, Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]

lemma dotProd_smul_right (c : ℝ) (x y : Fin d → ℝ) : dotProd x (c • y) = c * dotProd x y := by
  simp only [dotProd_comm x (c • y), dotProd_smul_left, dotProd_comm x y]

lemma dotProd_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℝ) (y : Fin d → ℝ) :
    dotProd (∑ i ∈ s, f i) y = ∑ i ∈ s, dotProd (f i) y := by
  simp only [dotProd, sum_apply, sum_mul, sum_comm (s := univ) (t := s)]

lemma dotProd_sum_right {ι : Type*} (s : Finset ι) (x : Fin d → ℝ) (f : ι → Fin d → ℝ) :
    dotProd x (∑ i ∈ s, f i) = ∑ i ∈ s, dotProd x (f i) := by
  simp only [dotProd, sum_apply, mul_sum, sum_comm (s := univ) (t := s)]

lemma dotProd_sum_smul_left {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → Fin d → ℝ) (y : Fin d → ℝ) :
    dotProd (∑ i ∈ s, w i • f i) y = ∑ i ∈ s, w i * dotProd (f i) y := by
  simp only [dotProd_sum_left, dotProd_smul_left]

lemma dotProd_sum_smul_right {ι : Type*} (s : Finset ι) (x : Fin d → ℝ) (w : ι → ℝ) (f : ι → Fin d → ℝ) :
    dotProd x (∑ i ∈ s, w i • f i) = ∑ i ∈ s, w i * dotProd x (f i) := by
  simp only [dotProd_sum_right, dotProd_smul_right]

lemma euclideanSq_eq_sum_sq (x : Fin d → ℝ) : euclideanSq x = ∑ i, (x i) ^ 2 := by
  simp [euclideanSq, dotProd, sq]

lemma euclideanSq_nonneg (x : Fin d → ℝ) : 0 ≤ euclideanSq x :=
  euclideanSq_eq_sum_sq x ▸ sum_nonneg fun i _ ↦ sq_nonneg (x i)

@[simp] lemma euclideanSq_zero : euclideanSq (0 : Fin d → ℝ) = 0 := by simp [euclideanSq]

lemma euclideanSq_eq_zero_iff (x : Fin d → ℝ) : euclideanSq x = 0 ↔ x = 0 := by
  rw [euclideanSq_eq_sum_sq, sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _]; simp [funext_iff]

lemma euclideanSq_pos_iff (x : Fin d → ℝ) : 0 < euclideanSq x ↔ x ≠ 0 := by
  simp [lt_iff_le_and_ne, euclideanSq_nonneg, ne_comm, euclideanSq_eq_zero_iff]

lemma euclideanSq_sub_self_eq_zero (x : Fin d → ℝ) : euclideanSq (x - x) = 0 := by
  rw [sub_self, euclideanSq_zero]

lemma euclideanSq_sub_comm (x y : Fin d → ℝ) : euclideanSq (x - y) = euclideanSq (y - x) := by
  simp only [euclideanSq_eq_sum_sq, Pi.sub_apply]; congr 1; ext i; ring

lemma euclideanSq_smul_add_smul (a b : ℝ) (v u : Fin d → ℝ) :
    euclideanSq (a • v + b • u) =
      a ^ 2 * euclideanSq v + 2 * a * b * dotProd v u + b ^ 2 * euclideanSq u := by
  simp only [euclideanSq, dotProd_add_left, dotProd_add_right, dotProd_smul_left, dotProd_smul_right,
    dotProd_comm u v]; ring

end ColorfulCaratheodory
