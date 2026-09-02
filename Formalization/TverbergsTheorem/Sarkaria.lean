import Formalization.TverbergsTheorem.Basis
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common

/-!
# Sarkaria's Algebraic Reduction and Radon's Theorem

This module formalizes Sarkaria's tensor lifting reduction and provides completed proofs
of Radon's theorem ($r = 2$) and low-order Tverberg partitions ($r \le 2$).

## Main Definitions & Theorems
* `sarkariaLift`: Sarkaria tensor lifting of a point with color index into $\mathbb{R}^{(d+1) \times m}$.
* `sarkaria_vector`: Standard literature alias for `sarkariaLift`.
* `projElim`: Projection eliminating a coordinate along a non-zero vector.
* `colorful_zero_sum_two`: Colorful Carathéodory zero-sum selection for 2-element color classes.
* `sarkaria_tverberg`: Sarkaria-Bárány algebraic reduction from zero-sum tensor combinations.
* `radons_theorem`: Classical Radon lemma ($r = 2$).
* `tverbergs_theorem_one`: Trivial Tverberg partition for $r = 1$.
* `tverbergs_theorem_le_two`: Tverberg's theorem for $r \le 2$.

## References
* K. S. Sarkaria (1992), *Tverberg's theorem via number of roots of polynomial systems*,
  Israel J. Math. 79:317–320.
* J. Radon (1921), *Mengen konvexer Körper, die einen gemeinsamen Punkt enthalten*,
  Math. Ann. 83:113–115.
-/

set_option linter.deprecated false

namespace TverbergsTheorem

open Finset BigOperators

variable {d r : ℕ}

/-- Sarkaria tensor lifting of a point x with color k into Fin (d + 1) → Fin m → ℝ. -/
def sarkariaLift (m : ℕ) (x : Fin d → ℝ) (k : Fin (m + 1)) : Fin (d + 1) → Fin m → ℝ :=
  fun i j ↦ (liftAffine x i) * (auxVec m k j)

/-- Standard literature alias for `sarkariaLift`. -/
abbrev sarkaria_vector (m : ℕ) (x : Fin d → ℝ) (k : Fin (m + 1)) : Fin (d + 1) → Fin m → ℝ :=
  sarkariaLift m x k

lemma sum_sarkariaLift_zero (m : ℕ) (x : Fin d → ℝ) :
    ∑ k : Fin (m + 1), sarkariaLift m x k = (0 : Fin (d + 1) → Fin m → ℝ) := by
  ext i j
  simp only [sarkariaLift, Finset.sum_apply, Pi.zero_apply, ← Finset.mul_sum]
  rw [show (∑ k : Fin (m + 1), auxVec m k j) = (∑ k : Fin (m + 1), auxVec m k) j by simp, sum_auxVec_zero]
  simp

lemma sum_fiberwise_univ {α β M : Type*} [DecidableEq β] [Fintype α] [Fintype β] [AddCommMonoid M]
    (k : α → β) (f : α → M) :
    ∑ i : α, f i = ∑ c : β, ∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), f i := by
  classical exact (Finset.sum_fiberwise Finset.univ k f).symm

lemma sarkaria_fiber_eq (m : ℕ) (N : ℕ)
    (x : Fin N → (Fin d → ℝ)) (k : Fin N → Fin (m + 1)) (w : Fin N → ℝ)
    (h_zero : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0)
    (j : Fin m) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ k i = Fin.castSucc j), w i • liftAffine (x i)) =
    (∑ i ∈ Finset.univ.filter (fun i ↦ k i = Fin.last m), w i • liftAffine (x i)) := by
  classical
  ext μ
  have hj := congr_fun (congr_fun h_zero μ) j
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sarkariaLift] at hj
  rw [sum_fiberwise_univ k (fun i ↦ w i * (liftAffine (x i) μ * auxVec m (k i) j))] at hj
  have h_fiber (c : Fin (m + 1)) :
      (∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), w i * (liftAffine (x i) μ * auxVec m (k i) j)) =
      (∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), w i * liftAffine (x i) μ) * auxVec m c j := by
    rw [Finset.sum_congr rfl (fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2, ← mul_assoc]), ← Finset.sum_mul]
  simp_rw [h_fiber] at hj
  have hk_ne : (Fin.castSucc j : Fin (m + 1)) ≠ Fin.last m := Fin.castSucc_ne_last j
  rw [Finset.sum_eq_add_of_mem (a := Fin.castSucc j) (b := Fin.last m) (Finset.mem_univ _) (Finset.mem_univ _) hk_ne] at hj
  · rw [auxVec_castSucc, auxVec_last] at hj
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hj ⊢
    linarith
  · intro x_c _ hx
    obtain ⟨t, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x_c
    · rw [auxVec_castSucc, Pi.single_eq_of_ne (fun ht ↦ hx.1 (by rw [ht])), mul_zero]
    · exact (hx.2 rfl).elim

lemma sarkaria_fiber_all_eq (m : ℕ) (N : ℕ)
    (x : Fin N → (Fin d → ℝ)) (k : Fin N → Fin (m + 1)) (w : Fin N → ℝ)
    (h_zero : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0)
    (c : Fin (m + 1)) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), w i • liftAffine (x i)) =
    (∑ i ∈ Finset.univ.filter (fun i ↦ k i = Fin.last m), w i • liftAffine (x i)) := by
  obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last c <;> [exact sarkaria_fiber_eq m N x k w h_zero j; rfl]

lemma sarkaria_partition_point (m : ℕ) (N : ℕ)
    (x : Fin N → (Fin d → ℝ)) (k : Fin N → Fin (m + 1)) (w : Fin N → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (h_zero : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0) :
    ∃ p : Fin d → ℝ, ∀ c : Fin (m + 1),
      p ∈ convexHull ℝ ((Finset.univ.filter (fun i ↦ k i = c)).image x : Set (Fin d → ℝ)) := by
  classical
  let I : Fin (m + 1) → Finset (Fin N) := fun c ↦ Finset.univ.filter (fun i ↦ k i = c)
  let V : Fin (d + 1) → ℝ := ∑ i ∈ I (Fin.last m), w i • liftAffine (x i)
  have hV_all (c : Fin (m + 1)) : (∑ i ∈ I c, w i • liftAffine (x i)) = V :=
    sarkaria_fiber_all_eq m N x k w h_zero c
  have h_weight (c : Fin (m + 1)) : (∑ i ∈ I c, w i) = V (Fin.last d) := by
    have h1 := congr_fun (hV_all c) (Fin.last d)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, liftAffine_last, mul_one] at h1
    exact h1
  have h_alpha_sum : (m + 1 : ℝ) * V (Fin.last d) = 1 := by
    calc (m + 1 : ℝ) * V (Fin.last d) = ∑ _c : Fin (m + 1), V (Fin.last d) := by
           rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]; push_cast; rfl
         _ = ∑ c : Fin (m + 1), ∑ i ∈ I c, w i := Finset.sum_congr rfl (fun c _ ↦ (h_weight c).symm)
         _ = 1 := by rw [← sum_fiberwise_univ, hw_sum]
  have h_alpha_val : V (Fin.last d) = (1 : ℝ) / (m + 1 : ℝ) :=
    eq_one_div_of_mul_eq_one_right h_alpha_sum
  have h_weight_pos (c : Fin (m + 1)) : 0 < ∑ i ∈ I c, w i := by
    rw [h_weight c, h_alpha_val]; positivity
  let p : Fin d → ℝ := fun t ↦ (m + 1 : ℝ) * V (Fin.castSucc t)
  refine ⟨p, fun c ↦ ?_⟩
  have hp_eq : p = (I c).centerMass w x := by
    dsimp [Finset.centerMass, p]; ext t
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have h_pts : (∑ i ∈ I c, w i * x i t) = V (Fin.castSucc t) := by
      have h1 := congr_fun (hV_all c) (Fin.castSucc t)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, liftAffine_castSucc] at h1
      exact h1
    rw [h_pts, h_weight c, h_alpha_val, one_div, inv_inv]
  rw [hp_eq]
  exact Finset.centerMass_mem_convexHull (I c) (fun i _ ↦ hw_nonneg i) (h_weight_pos c)
    (fun i hi ↦ Finset.mem_coe.mpr (Finset.mem_image_of_mem x hi))

/-- Projection eliminating coordinate j₀ along a non-zero vector u. -/
noncomputable def projElim (D : ℕ) (j₀ : Fin (D + 1)) (u v : Fin (D + 1) → ℝ) : Fin D → ℝ :=
  fun t ↦ v (j₀.succAbove t) - (u (j₀.succAbove t) / u j₀) * v j₀

lemma projElim_add (D : ℕ) (j₀ : Fin (D + 1)) (u v₁ v₂ : Fin (D + 1) → ℝ) :
    projElim D j₀ u (v₁ + v₂) = projElim D j₀ u v₁ + projElim D j₀ u v₂ := by
  ext; dsimp [projElim]; ring

lemma projElim_smul (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (c : ℝ) (v : Fin (D + 1) → ℝ) :
    projElim D j₀ u (c • v) = c • projElim D j₀ u v := by
  ext; dsimp [projElim]; ring

lemma projElim_self (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (hu : u j₀ ≠ 0) :
    projElim D j₀ u u = 0 := by
  ext t; dsimp [projElim]; rw [div_mul_cancel₀ _ hu, sub_self]

lemma projElim_sum {ι : Type*} (s : Finset ι) (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ)
    (f : ι → Fin (D + 1) → ℝ) :
    projElim D j₀ u (∑ i ∈ s, f i) = ∑ i ∈ s, projElim D j₀ u (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext; simp [projElim]
  · intro i s hi ih; rw [Finset.sum_insert hi, Finset.sum_insert hi, projElim_add, ih]

lemma projElim_eq_zero_iff (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (hu : u j₀ ≠ 0)
    (v : Fin (D + 1) → ℝ) :
    projElim D j₀ u v = 0 ↔ v = (v j₀ / u j₀) • u := by
  constructor
  · intro h; ext j
    have h_all : ∀ k : Fin (D + 1), v k = ((v j₀ / u j₀) • u) k := by
      rw [Fin.forall_iff_succAbove j₀]
      refine ⟨by simp [div_mul_cancel₀ _ hu], fun t ↦ by
        have ht := congr_fun h t; dsimp [projElim] at ht
        have : u (j₀.succAbove t) / u j₀ * v j₀ = (v j₀ / u j₀) * u (j₀.succAbove t) := by ring
        rw [this] at ht; dsimp; linarith⟩
    exact h_all j
  · intro hv; rw [hv, projElim_smul, projElim_self D j₀ u hu, smul_zero]

lemma colorful_zero_sum_two (D : ℕ) : ∀ (N : ℕ) (_hN : D + 1 ≤ N)
    (v : Fin N → Fin 2 → (Fin D → ℝ))
    (_hv : ∀ i : Fin N, ∑ k : Fin 2, v i k = 0),
    ∃ (k : Fin N → Fin 2) (w : Fin N → ℝ),
      (∀ i, 0 ≤ w i) ∧
      (∑ i, w i = 1) ∧
      (∑ i, w i • v i (k i) = 0) := by
  classical
  induction D with
  | zero =>
    intro N hN v _hv
    have hN_pos : 0 < N := by omega
    refine ⟨fun _ ↦ 0, fun i ↦ if i = ⟨0, hN_pos⟩ then 1 else 0,
      fun i ↦ by dsimp; split_ifs <;> linarith, ?_, funext fun t ↦ Fin.elim0 t⟩
    dsimp; rw [Finset.sum_eq_single ⟨0, hN_pos⟩]
    · rw [if_pos rfl]
    · intro i _ hi; rw [if_neg hi]
    · intro h; exact (h (Finset.mem_univ _)).elim
  | succ D ih =>
    intro N hN v hv
    have hN_pos : 0 < N := by omega
    let i0 : Fin N := ⟨N - 1, by omega⟩
    let k0 : Fin 2 := 0
    by_cases hu : v i0 k0 = 0
    · refine ⟨fun _ ↦ k0, fun i ↦ if i = i0 then 1 else 0,
        fun i ↦ by dsimp; split_ifs <;> linarith, ?_, ?_⟩
      · dsimp; rw [Finset.sum_eq_single i0]
        · rw [if_pos rfl]
        · intro i _ hi; rw [if_neg hi]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · dsimp; rw [Finset.sum_eq_single i0]
        · rw [if_pos rfl, one_smul, hu]
        · intro i _ hi; rw [if_neg hi, zero_smul]
        · intro h; exact (h (Finset.mem_univ _)).elim
    · obtain ⟨j0, hj0_ne⟩ : ∃ j : Fin (D + 1), v i0 k0 j ≠ 0 := by
        contrapose! hu; ext j; exact hu j
      let N' := N - 1
      have hN_eq : N = N' + 1 := by omega
      let eN : Fin (N' + 1) ≃ Fin N := finCongr hN_eq.symm
      let v' : Fin N' → Fin 2 → (Fin D → ℝ) :=
        fun i k ↦ projElim D j0 (v i0 k0) (v (eN (Fin.castSucc i)) k)
      have hv' : ∀ i : Fin N', ∑ k : Fin 2, v' i k = 0 := by
        intro i; dsimp [v']; rw [← projElim_sum, hv (eN (Fin.castSucc i))]
        ext t; dsimp [projElim]; ring
      obtain ⟨k', w', hw'_nonneg, hw'_sum, h_zero'⟩ := ih N' (by omega) v' hv'
      let Z : Fin (D + 1) → ℝ := ∑ i : Fin N', w' i • v (eN (Fin.castSucc i)) (k' i)
      have hZ_proj : projElim D j0 (v i0 k0) Z = 0 := by
        dsimp [Z]; rw [projElim_sum]
        have : (∑ i : Fin N', projElim D j0 (v i0 k0) (w' i • v (eN (Fin.castSucc i)) (k' i))) =
               ∑ i : Fin N', w' i • v' i (k' i) := Finset.sum_congr rfl fun i _ ↦ projElim_smul D j0 (v i0 k0) (w' i) _
        rw [this, h_zero']
      have hZ_eq : Z = (Z j0 / v i0 k0 j0) • v i0 k0 :=
        (projElim_eq_zero_iff D j0 (v i0 k0) hj0_ne Z).mp hZ_proj
      let c := Z j0 / v i0 k0 j0
      by_cases hc : c ≤ 0
      · let k_raw : Fin (N' + 1) → Fin 2 := Fin.lastCases k0 (fun i ↦ k' i)
        let w_raw : Fin (N' + 1) → ℝ := Fin.lastCases ((-c) / (1 - c)) (fun i ↦ w' i / (1 - c))
        let k : Fin N → Fin 2 := fun i ↦ k_raw (eN.symm i)
        let w : Fin N → ℝ := fun i ↦ w_raw (eN.symm i)
        have hc_denom : 0 < 1 - c := by linarith
        refine ⟨k, w, ?_, ?_, ?_⟩
        · intro i; dsimp [w, w_raw]; refine Fin.lastCases ?_ ?_ (eN.symm i)
          · rw [Fin.lastCases_last]; exact div_nonneg (by linarith) (by linarith)
          · intro j; rw [Fin.lastCases_castSucc]; exact div_nonneg (hw'_nonneg j) (by linarith)
        · dsimp [w, w_raw]; rw [← eN.sum_comp, Fin.sum_univ_castSucc]
          simp only [Equiv.symm_apply_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          have : (∑ j : Fin N', w' j / (1 - c)) = (∑ j : Fin N', w' j) / (1 - c) := by
            simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
          rw [this, hw'_sum]
          have : 1 / (1 - c) + -c / (1 - c) = (1 - c) / (1 - c) := by ring
          rw [this]; exact div_self (ne_of_gt hc_denom)
        · dsimp [k, w, k_raw, w_raw]; rw [← eN.sum_comp, Fin.sum_univ_castSucc]
          simp only [Equiv.symm_apply_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          have h_cast : (∑ j : Fin N', (w' j / (1 - c)) • v (eN (Fin.castSucc j)) (k' j)) = (1 / (1 - c)) • Z := by
            dsimp [Z]; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ ↦ by
              simp only [smul_smul]; congr 1; ring
          have heN_last : eN (Fin.last N') = i0 := rfl
          rw [heN_last, h_cast, hZ_eq]
          dsimp [c]; simp only [smul_smul]
          have : (1 / (1 - c)) * (Z j0 / v i0 k0 j0) + - (Z j0 / v i0 k0 j0) / (1 - c) = 0 := by ring
          rw [← add_smul, this, zero_smul]
      · let k1 : Fin 2 := 1
        let k_raw : Fin (N' + 1) → Fin 2 := Fin.lastCases k1 (fun i ↦ k' i)
        let w_raw : Fin (N' + 1) → ℝ := Fin.lastCases (c / (1 + c)) (fun i ↦ w' i / (1 + c))
        let k : Fin N → Fin 2 := fun i ↦ k_raw (eN.symm i)
        let w : Fin N → ℝ := fun i ↦ w_raw (eN.symm i)
        have hc_denom : 0 < 1 + c := by linarith
        refine ⟨k, w, ?_, ?_, ?_⟩
        · intro i; dsimp [w, w_raw]; refine Fin.lastCases ?_ ?_ (eN.symm i)
          · rw [Fin.lastCases_last]; exact div_nonneg (by linarith) (by linarith)
          · intro j; rw [Fin.lastCases_castSucc]; exact div_nonneg (hw'_nonneg j) (by linarith)
        · dsimp [w, w_raw]; rw [← eN.sum_comp, Fin.sum_univ_castSucc]
          simp only [Equiv.symm_apply_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          have : (∑ j : Fin N', w' j / (1 + c)) = (∑ j : Fin N', w' j) / (1 + c) := by
            simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
          rw [this, hw'_sum]
          have : 1 / (1 + c) + c / (1 + c) = (1 + c) / (1 + c) := by ring
          rw [this]; exact div_self (ne_of_gt hc_denom)
        · dsimp [k, w, k_raw, w_raw]; rw [← eN.sum_comp, Fin.sum_univ_castSucc]
          simp only [Equiv.symm_apply_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
          have h_cast : (∑ j : Fin N', (w' j / (1 + c)) • v (eN (Fin.castSucc j)) (k' j)) = (1 / (1 + c)) • Z := by
            dsimp [Z]; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ ↦ by
              simp only [smul_smul]; congr 1; ring
          have heN_last : eN (Fin.last N') = i0 := rfl
          rw [heN_last, h_cast, hZ_eq]
          dsimp [c]; simp only [smul_smul]
          have h_coeff : 1 / (1 + (Z j0 / v i0 k0 j0)) * (Z j0 / v i0 k0 j0) = (Z j0 / v i0 k0 j0) / (1 + (Z j0 / v i0 k0 j0)) := by ring
          rw [h_coeff, ← smul_add]
          have h_sum := hv i0
          have h_fin2 : (∑ k : Fin 2, v i0 k) = v i0 k0 + v i0 k1 := Fin.sum_univ_two (v i0)
          rw [h_fin2] at h_sum
          rw [h_sum, smul_zero]

/-- Sarkaria-Bárány reduction: given a zero sum of lifted vectors, an explicit Tverberg partition exists. -/
theorem sarkaria_tverberg (m : ℕ)
    (S : Finset (Fin d → ℝ)) (N : ℕ) (_hN_card : S.card = N)
    (k : Fin N → Fin (m + 1))
    (w : Fin N → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (e : Fin N ≃ S)
    (h_zero_lift : (∑ i : Fin N, w i • sarkariaLift m (e i : Fin d → ℝ) (k i)) = 0) :
    ∃ P : Fin (m + 1) → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  classical
  let x : Fin N → Fin d → ℝ := fun i ↦ (e i : Fin d → ℝ)
  have hx_inj : Function.Injective x := fun i1 i2 heq ↦ e.injective (Subtype.ext heq)
  let I : Fin (m + 1) → Finset (Fin N) := fun c ↦ Finset.univ.filter (fun i ↦ k i = c)
  let P : Fin (m + 1) → Finset (Fin d → ℝ) := fun c ↦ (I c).image x
  obtain ⟨p, hp⟩ := sarkaria_partition_point m N x k w hw_nonneg hw_sum h_zero_lift
  refine ⟨P, fun c y hy ↦ by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy; exact (e i).2,
    fun i j hij ↦ by
      rw [Finset.disjoint_iff_ne]; rintro y1 hy1 y2 hy2 rfl
      obtain ⟨i1, hi1, rfl⟩ := Finset.mem_image.mp hy1
      obtain ⟨i2, hi2, heq⟩ := Finset.mem_image.mp hy2
      obtain rfl := hx_inj heq.symm
      exact hij (((Finset.mem_filter.mp hi1).2.symm.trans (Finset.mem_filter.mp hi2).2)),
    ?_,
    ⟨p, Set.mem_iInter.mpr hp⟩⟩
  ext y; constructor
  · intro hy; obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hy; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc; exact (e i).2
  · intro hy; exact Finset.mem_biUnion.mpr ⟨k (e.symm ⟨y, hy⟩), Finset.mem_univ _,
      Finset.mem_image.mpr ⟨e.symm ⟨y, hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, by simp [x]⟩⟩

/-- **Radon's Lemma** (Tverberg's Theorem for r = 2):
Any set of d + 2 points in ℝ^d can be partitioned into 2 disjoint sets with intersecting convex hulls. -/
theorem radons_theorem
    (S : Finset (Fin d → ℝ)) (hS : S.card = (2 - 1) * (d + 1) + 1) :
    ∃ P : Fin 2 → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  classical
  let m := 1
  have hm : 1 ≤ m := by omega
  let N := m * (d + 1) + 1
  have hN_eq : N = (2 - 1) * (d + 1) + 1 := rfl
  have h_card : Fintype.card S = N := by rw [Fintype.card_coe, hS, hN_eq]
  let e : Fin N ≃ S := (Fintype.equivFinOfCardEq h_card).symm
  let x : Fin N → Fin d → ℝ := fun i ↦ (e i : Fin d → ℝ)
  let D := (d + 1) * m
  let matToVec : (Fin (d + 1) → Fin m → ℝ) → (Fin D → ℝ) :=
    fun M t ↦ M (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  have h_mat_inj : Function.Injective matToVec := fun M1 M2 heq ↦ by
    ext i j; have ht := congr_fun heq (finProdFinEquiv (i, j))
    dsimp [matToVec] at ht; rwa [Equiv.symm_apply_apply] at ht
  let v : Fin N → Fin 2 → (Fin D → ℝ) := fun i k ↦
    if k = 0 then matToVec (sarkariaLift m (x i) (Fin.last m))
    else - matToVec (sarkariaLift m (x i) (Fin.last m))
  have hv (i : Fin N) : ∑ k : Fin 2, v i k = 0 := by
    rw [Fin.sum_univ_two]; dsimp [v]; ring
  obtain ⟨k2, w, hw_nonneg, hw_sum, h_zero_v⟩ := colorful_zero_sum_two D N (by dsimp [D, N]; rw [mul_comm (d + 1) m]) v hv
  let k : Fin N → Fin (m + 1) := fun i ↦
    if k2 i = 0 then Fin.last m else Fin.castSucc ⟨0, hm⟩
  have h_lift (i : Fin N) : sarkariaLift m (x i) (k i) =
      if k2 i = 0 then sarkariaLift m (x i) (Fin.last m) else -sarkariaLift m (x i) (Fin.last m) := by
    dsimp [k]; split_ifs with hk0 <;> [rfl; ext a b]
    dsimp [sarkariaLift]
    have h0_eq : (0 : Fin (m + 1)) = Fin.castSucc ⟨0, hm⟩ := rfl
    rw [h0_eq, auxVec_castSucc, auxVec_last, Subsingleton.elim b ⟨0, hm⟩, Pi.single_eq_same]
    ring
  have h_zero_lift : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0 := by
    apply h_mat_inj; ext t
    have ht := congr_fun h_zero_v t
    simp only [matToVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht ⊢
    rw [← ht]; refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h_lift i]
    dsimp [v, matToVec]
    split_ifs <;> rfl
  exact sarkaria_tverberg m S N (by rw [hS, hN_eq]) k w hw_nonneg hw_sum e h_zero_lift

/-- **Trivial Tverberg's Theorem** (r = 1):
Any non-empty set S in ℝ^d can be partitioned into 1 set (itself) with non-empty convex hull. -/
theorem tverbergs_theorem_one
    (S : Finset (Fin d → ℝ)) (hS : S.card = (1 - 1) * (d + 1) + 1) :
    ∃ P : Fin 1 → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  classical
  obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨fun _ ↦ S, fun _ ↦ Subset.refl S, fun i j hij ↦ (hij (Subsingleton.elim i j)).elim,
    by ext; simp, ⟨x, Set.mem_iInter.mpr fun _ ↦ subset_convexHull ℝ (S : Set (Fin d → ℝ)) hx⟩⟩

/-- **Tverberg's Theorem** for r ≤ 2 (including Radon's Theorem for r = 2 and trivial partition for r = 1). -/
theorem tverbergs_theorem_le_two (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (S : Finset (Fin d → ℝ)) (hS : S.card = (r - 1) * (d + 1) + 1) :
    ∃ P : Fin r → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  rcases eq_or_lt_of_le hr1 with rfl | hr_gt
  · exact tverbergs_theorem_one S hS
  · have : r = 2 := by omega
    subst this
    exact radons_theorem S hS

end TverbergsTheorem
