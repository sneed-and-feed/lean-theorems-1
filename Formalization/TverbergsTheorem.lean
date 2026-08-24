import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
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
# Tverberg's Theorem: Reductions and the Full One-Dimensional Case

Tverberg's theorem (H. Tverberg, 1966) is a foundational result in discrete and combinatorial
geometry generalizing Radon's lemma ($r = 2$).  The completed unconditional declarations in this
module cover $r \le 2$ in arbitrary dimension and every $r$ in dimension one.  The general
higher-dimensional statement is represented by a conditional Sarkaria reduction, not claimed as
a completed proof here.

## Mathematical Statement

Let $d \ge 1$ and $r \ge 1$. Any set $S \subset \mathbb{R}^d$ of cardinality:
$$N = (r - 1)(d + 1) + 1$$
can be partitioned into $r$ pairwise disjoint subsets $A_1, \dots, A_r$ whose convex hulls
share a common point of intersection:
$$\bigcap_{i=1}^r \operatorname{conv}(A_i) \ne \emptyset$$

## References

* H. Tverberg (1966), *A generalization of Radon's theorem*, J. London Math. Soc. 41:123–128,
  Theorem 1. https://doi.org/10.1112/jlms/s1-41.1.123
* W. Mulzer and D. Werner (2013), *Approximating Tverberg points in linear time for any fixed
  dimension*, Discrete Comput. Geom. 50:520–535, §2.2, Lemma 2.3 and Theorem 2.4.
  https://doi.org/10.1007/s00454-013-9528-7
  The proof of `tverberg_1d` uses symmetric-rank pairing as a canonical specialization of their
  median-and-opposite-sides construction.
* J. Matoušek (2002), *Lectures on Discrete Geometry*, GTM 212, Springer, Chapter 8.
-/

set_option linter.deprecated false

namespace TverbergsTheorem

open Finset BigOperators

variable {d r : ℕ}

/-- Standard auxiliary basis vectors in ℝ^m with zero sum. -/
def auxVec (m : ℕ) (k : Fin (m + 1)) : Fin m → ℝ :=
  if h : k.1 < m then Pi.single ⟨k.1, h⟩ 1 else fun _ ↦ -1

lemma auxVec_castSucc (m : ℕ) (j : Fin m) : auxVec m (Fin.castSucc j) = Pi.single j 1 := by
  dsimp [auxVec]
  split_ifs with h
  · congr
  · have hj := j.2; omega

lemma auxVec_last (m : ℕ) : auxVec m (Fin.last m) = fun _ ↦ -1 := by
  dsimp [auxVec]
  split_ifs with h
  · omega
  · rfl

lemma sum_auxVec_zero (m : ℕ) : ∑ k : Fin (m + 1), auxVec m (k : Fin (m + 1)) = (0 : Fin m → ℝ) := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [auxVec_castSucc, auxVec_last]
  ext j
  simp only [Finset.sum_apply, Pi.add_apply, Pi.zero_apply]
  rw [Finset.sum_pi_single j (fun _ ↦ (1 : ℝ)) (s := Finset.univ)]
  simp

/-- Lifted point in affine space ℝ^{d+1}. -/
def liftAffine (x : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc x 1

lemma liftAffine_last (x : Fin d → ℝ) : liftAffine x (Fin.last d) = 1 := by
  simp [liftAffine, Fin.snoc]

lemma liftAffine_castSucc (x : Fin d → ℝ) (t : Fin d) : liftAffine x (Fin.castSucc t) = x t := by
  simp [liftAffine, Fin.snoc]

/-- Sarkaria tensor lifting of a point x with color k into Fin (d + 1) → Fin m → ℝ. -/
def sarkariaLift (m : ℕ) (x : Fin d → ℝ) (k : Fin (m + 1)) : Fin (d + 1) → Fin m → ℝ :=
  fun i j ↦ (liftAffine x i) * (auxVec m k j)

lemma sum_sarkariaLift_zero (m : ℕ) (x : Fin d → ℝ) :
    ∑ k : Fin (m + 1), sarkariaLift m x k = (0 : Fin (d + 1) → Fin m → ℝ) := by
  ext i j
  simp only [sarkariaLift, Finset.sum_apply, Pi.zero_apply]
  rw [← Finset.mul_sum]
  have h := congr_fun (sum_auxVec_zero m) j
  simp only [Finset.sum_apply, Pi.zero_apply] at h
  rw [h, mul_zero]

lemma sum_fiberwise_univ {α β M : Type*} [DecidableEq β] [Fintype α] [Fintype β] [AddCommMonoid M]
    (k : α → β) (f : α → M) :
    ∑ i : α, f i = ∑ c : β, ∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), f i := by
  classical
  exact (Finset.sum_fiberwise Finset.univ k f).symm

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
  have h_fiber : ∀ c : Fin (m + 1),
      (∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), w i * (liftAffine (x i) μ * auxVec m (k i) j)) =
      (∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), w i * liftAffine (x i) μ) * auxVec m c j := by
    intro c
    have h_term : ∀ i ∈ Finset.univ.filter (fun i ↦ k i = c),
        w i * (liftAffine (x i) μ * auxVec m (k i) j) =
        (w i * liftAffine (x i) μ) * auxVec m c j := by
      intro i hi
      have hki : k i = c := (Finset.mem_filter.mp hi).2
      rw [hki, mul_assoc]
    rw [Finset.sum_congr rfl h_term, ← Finset.sum_mul]
  simp_rw [h_fiber] at hj
  let k0 : Fin (m + 1) := Fin.castSucc j
  let k1 : Fin (m + 1) := Fin.last m
  have hk_ne : k0 ≠ k1 := by
    intro h; have := congr_arg Fin.val h; dsimp [k0, k1, Fin.last, Fin.castSucc] at this; omega
  rw [Finset.sum_eq_add_of_mem (a := k0) (b := k1) (Finset.mem_univ _) (Finset.mem_univ _) hk_ne] at hj
  · rw [auxVec_castSucc, auxVec_last] at hj
    simp only [Pi.single_eq_same] at hj
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    linarith
  · intro x _ hx
    have hx0 : ¬(x = Fin.castSucc j) := hx.1
    have hxm : ¬(x = Fin.last m) := hx.2
    obtain ⟨t, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last x
    · rw [auxVec_castSucc]
      have ht_ne : t ≠ j := by intro h; subst h; exact hx0 rfl
      rw [Pi.single_apply]
      split_ifs with heq
      · exact (ht_ne heq.symm).elim
      · rw [mul_zero]
    · exact (hxm rfl).elim

lemma sarkaria_fiber_all_eq (m : ℕ) (N : ℕ)
    (x : Fin N → (Fin d → ℝ)) (k : Fin N → Fin (m + 1)) (w : Fin N → ℝ)
    (h_zero : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0)
    (c : Fin (m + 1)) :
    (∑ i ∈ Finset.univ.filter (fun i ↦ k i = c), w i • liftAffine (x i)) =
    (∑ i ∈ Finset.univ.filter (fun i ↦ k i = Fin.last m), w i • liftAffine (x i)) := by
  obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last c
  · exact sarkaria_fiber_eq m N x k w h_zero j
  · rfl

lemma sarkaria_partition_point (m : ℕ) (N : ℕ)
    (x : Fin N → (Fin d → ℝ)) (k : Fin N → Fin (m + 1)) (w : Fin N → ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (h_zero : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0) :
    ∃ p : Fin d → ℝ, ∀ c : Fin (m + 1),
      p ∈ convexHull ℝ ((Finset.univ.filter (fun i ↦ k i = c)).image x : Set (Fin d → ℝ)) := by
  classical
  let I : Fin (m + 1) → Finset (Fin N) := fun c ↦ Finset.univ.filter (fun i ↦ k i = c)
  let V : Fin (d + 1) → ℝ := ∑ i ∈ I (Fin.last m), w i • liftAffine (x i)
  have hV_all : ∀ c : Fin (m + 1), (∑ i ∈ I c, w i • liftAffine (x i)) = V := by
    intro c
    exact sarkaria_fiber_all_eq m N x k w h_zero c
  have h_weight : ∀ c : Fin (m + 1), (∑ i ∈ I c, w i) = V (Fin.last d) := by
    intro c
    have h1 := congr_fun (hV_all c) (Fin.last d)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : ∀ i ∈ I c, w i * liftAffine (x i) (Fin.last d) = w i := by
      intro i _
      rw [liftAffine_last, mul_one]
    rw [Finset.sum_congr rfl h2] at h1
    exact h1
  have h_alpha_sum : (m + 1 : ℝ) * V (Fin.last d) = 1 := by
    calc (m + 1 : ℝ) * V (Fin.last d) = ∑ c : Fin (m + 1), V (Fin.last d) := by
           rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
           push_cast; rfl
         _ = ∑ c : Fin (m + 1), ∑ i ∈ I c, w i := by
           apply Finset.sum_congr rfl; intro c _; rw [h_weight c]
         _ = ∑ i : Fin N, w i := (sum_fiberwise_univ k w).symm
         _ = 1 := hw_sum
  have hm_pos : 0 < (m + 1 : ℝ) := by positivity
  have h_alpha_val : V (Fin.last d) = (1 : ℝ) / (m + 1 : ℝ) := by
    exact eq_one_div_of_mul_eq_one_right h_alpha_sum
  have h_weight_pos : ∀ c : Fin (m + 1), 0 < ∑ i ∈ I c, w i := by
    intro c
    rw [h_weight c, h_alpha_val]
    positivity
  let p : Fin d → ℝ := fun t ↦ (m + 1 : ℝ) * V (Fin.castSucc t)
  refine ⟨p, ?_⟩
  intro c
  have hp_eq : p = (I c).centerMass w x := by
    dsimp [Finset.centerMass, p]
    ext t
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have h_pts : (∑ i ∈ I c, w i * x i t) = V (Fin.castSucc t) := by
      have h1 := congr_fun (hV_all c) (Fin.castSucc t)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : ∀ i ∈ I c, w i * liftAffine (x i) (Fin.castSucc t) = w i * x i t := by
        intro i _
        rw [liftAffine_castSucc]
      rw [Finset.sum_congr rfl h2] at h1
      exact h1
    rw [h_pts, h_weight c, h_alpha_val, one_div, inv_inv]
  rw [hp_eq]
  apply Finset.centerMass_mem_convexHull (I c) (fun i _ ↦ hw_nonneg i) (h_weight_pos c)
  intro i hi
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem x hi)

/-- Projection eliminating coordinate j₀ along a non-zero vector u. -/
noncomputable def projElim (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (v : Fin (D + 1) → ℝ) : Fin D → ℝ :=
  fun t ↦ v (j₀.succAbove t) - (u (j₀.succAbove t) / u j₀) * v j₀

lemma projElim_add (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (v₁ v₂ : Fin (D + 1) → ℝ) :
    projElim D j₀ u (v₁ + v₂) = projElim D j₀ u v₁ + projElim D j₀ u v₂ := by
  ext t; dsimp [projElim]; ring

lemma projElim_smul (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (c : ℝ) (v : Fin (D + 1) → ℝ) :
    projElim D j₀ u (c • v) = c • projElim D j₀ u v := by
  ext t; dsimp [projElim]; ring

lemma projElim_self (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (hu : u j₀ ≠ 0) :
    projElim D j₀ u u = 0 := by
  ext t
  dsimp [projElim]
  have : u (j₀.succAbove t) / u j₀ * u j₀ = u (j₀.succAbove t) := div_mul_cancel₀ (u (j₀.succAbove t)) hu
  rw [this, sub_self]

lemma projElim_sum {ι : Type*} (s : Finset ι) (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ)
    (f : ι → Fin (D + 1) → ℝ) :
    projElim D j₀ u (∑ i ∈ s, f i) = ∑ i ∈ s, projElim D j₀ u (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext t; simp [projElim]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, projElim_add, ih]

lemma projElim_eq_zero_iff (D : ℕ) (j₀ : Fin (D + 1)) (u : Fin (D + 1) → ℝ) (hu : u j₀ ≠ 0)
    (v : Fin (D + 1) → ℝ) :
    projElim D j₀ u v = 0 ↔ v = (v j₀ / u j₀) • u := by
  constructor
  · intro h
    ext j
    have h_all : ∀ k : Fin (D + 1), v k = ((v j₀ / u j₀) • u) k := by
      rw [Fin.forall_iff_succAbove j₀]
      constructor
      · simp only [Pi.smul_apply, smul_eq_mul]
        rw [div_mul_cancel₀ (v j₀) hu]
      · intro t
        have ht := congr_fun h t
        dsimp [projElim] at ht
        have h_comm : u (j₀.succAbove t) / u j₀ * v j₀ = (v j₀ / u j₀) * u (j₀.succAbove t) := by ring
        rw [h_comm] at ht
        dsimp
        linarith
    exact h_all j
  · intro hv
    rw [hv, projElim_smul, projElim_self D j₀ u hu, smul_zero]

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
    intro N _hN v _hv
    have hN_pos : 0 < N := by omega
    let k0 : Fin 2 := ⟨0, by omega⟩
    let k : Fin N → Fin 2 := fun _ ↦ k0
    let w : Fin N → ℝ := fun i ↦ if i = ⟨0, hN_pos⟩ then 1 else 0
    refine ⟨k, w, ?_, ?_, ?_⟩
    · intro i; dsimp [w]; split_ifs <;> linarith
    · dsimp [w]
      rw [Finset.sum_eq_single ⟨0, hN_pos⟩]
      · rw [if_pos rfl]
      · intro i _ hi; rw [if_neg hi]
      · intro h_not; exact (h_not (Finset.mem_univ _)).elim
    · ext t; exact Fin.elim0 t
  | succ D ih =>
    intro N hN v hv
    have hN_pos : 0 < N := by omega
    let i0 : Fin N := ⟨N - 1, by omega⟩
    let k0 : Fin 2 := ⟨0, by omega⟩
    by_cases hu : v i0 k0 = 0
    · refine ⟨fun _ ↦ k0, fun i ↦ if i = i0 then 1 else 0, ?_, ?_, ?_⟩
      · intro i; dsimp; split_ifs <;> linarith
      · dsimp
        rw [Finset.sum_eq_single i0]
        · rw [if_pos rfl]
        · intro i _ hi; rw [if_neg hi]
        · intro h_not; exact (h_not (Finset.mem_univ _)).elim
      · dsimp
        rw [Finset.sum_eq_single i0]
        · rw [if_pos rfl, one_smul, hu]
        · intro i _ hi; rw [if_neg hi, zero_smul]
        · intro h_not; exact (h_not (Finset.mem_univ _)).elim
    · have hj0 : ∃ j : Fin (D + 1), v i0 k0 j ≠ 0 := by
        by_contra h_all_zero
        have : v i0 k0 = 0 := by
          ext j; by_contra hj; exact h_all_zero ⟨j, hj⟩
        exact hu this
      obtain ⟨j0, hj0_ne⟩ := hj0
      let N' := N - 1
      have hN_eq : N = N' + 1 := by omega
      let eN : Fin (N' + 1) ≃ Fin N := finCongr hN_eq.symm
      have hN' : D + 1 ≤ N' := by omega
      let v' : Fin N' → Fin 2 → (Fin D → ℝ) :=
        fun i k ↦ projElim D j0 (v i0 k0) (v (eN (Fin.castSucc i)) k)
      have hv' : ∀ i : Fin N', ∑ k : Fin 2, v' i k = 0 := by
        intro i; dsimp [v']
        rw [← projElim_sum, hv (eN (Fin.castSucc i))]
        ext t; dsimp [projElim]; ring
      obtain ⟨k', w', hw'_nonneg, hw'_sum, h_zero'⟩ := ih N' hN' v' hv'
      let Z : Fin (D + 1) → ℝ := ∑ i : Fin N', w' i • v (eN (Fin.castSucc i)) (k' i)
      have hZ_proj : projElim D j0 (v i0 k0) Z = 0 := by
        dsimp [Z]; rw [projElim_sum]
        have : (∑ i : Fin N', projElim D j0 (v i0 k0) (w' i • v (eN (Fin.castSucc i)) (k' i))) =
               ∑ i : Fin N', w' i • v' i (k' i) := by
          apply Finset.sum_congr rfl; intro i _; rw [projElim_smul]
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
          have h_cast : (∑ j : Fin N', (w' j / (1 - c)) • v (eN (Fin.castSucc j)) (k' j)) =
                        (1 / (1 - c)) • Z := by
            dsimp [Z]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
            simp only [smul_smul]; congr 1; ring
          have heN_last : eN (Fin.last N') = i0 := rfl
          rw [heN_last, h_cast, hZ_eq]
          dsimp [c]; simp only [smul_smul]
          have : (1 / (1 - c)) * (Z j0 / v i0 k0 j0) + - (Z j0 / v i0 k0 j0) / (1 - c) = 0 := by ring
          rw [← add_smul, this, zero_smul]
      · let k1 : Fin 2 := ⟨1, by omega⟩
        have hk1_ne : k1 ≠ k0 := by
          intro h_eq
          have : k1.1 = k0.1 := congr_arg Fin.val h_eq
          dsimp [k1, k0] at this
          contradiction
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
          have h_cast : (∑ j : Fin N', (w' j / (1 + c)) • v (eN (Fin.castSucc j)) (k' j)) =
                        (1 / (1 + c)) • Z := by
            dsimp [Z]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
            simp only [smul_smul]; congr 1; ring
          have heN_last : eN (Fin.last N') = i0 := rfl
          rw [heN_last, h_cast, hZ_eq]
          dsimp [c]; simp only [smul_smul]
          have : (1 / (1 + (Z j0 / v i0 k0 j0)) * (Z j0 / v i0 k0 j0)) • v i0 k0 +
                 ((Z j0 / v i0 k0 j0) / (1 + (Z j0 / v i0 k0 j0))) • v i0 k1 = 0 := by
            have h_coeff : 1 / (1 + (Z j0 / v i0 k0 j0)) * (Z j0 / v i0 k0 j0) =
                           (Z j0 / v i0 k0 j0) / (1 + (Z j0 / v i0 k0 j0)) := by ring
            rw [h_coeff, ← smul_add]
            have h_sum := hv i0
            have h_fin2 : (∑ k : Fin 2, v i0 k) = v i0 k0 + v i0 k1 := by
              rw [Finset.sum_eq_add_of_mem (a := k0) (b := k1) (Finset.mem_univ _) (Finset.mem_univ _) hk1_ne.symm]
              intro x _ hx
              have : x = k0 ∨ x = k1 := by
                have h_card : ({k0, k1} : Finset (Fin 2)).card = 2 := by
                  rw [Finset.card_pair hk1_ne.symm]
                have : ({k0, k1} : Finset (Fin 2)) = Finset.univ :=
                  Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by rw [h_card, Finset.card_univ, Fintype.card_fin])
                have hx_univ : x ∈ ({k0, k1} : Finset (Fin 2)) := by rw [this]; exact Finset.mem_univ x
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx_univ
                exact hx_univ
              rcases this with rfl | rfl
              · exact (hx.1 rfl).elim
              · exact (hx.2 rfl).elim
            rw [h_fin2] at h_sum
            rw [h_sum, smul_zero]
          exact this

/-- **Tverberg's Partition Property:**
A collection of `r` pairwise disjoint subsets of `S` that partition `S`
and whose convex hulls have a non-empty intersection. -/
def IsTverbergPartition (S : Finset (Fin d → ℝ)) (P : Fin r → Finset (Fin d → ℝ)) : Prop :=
  (∀ i, P i ⊆ S) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  (Finset.biUnion Finset.univ P = S) ∧
  (⋂ i : Fin r, convexHull ℝ (P i : Set (Fin d → ℝ))).Nonempty

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
  refine ⟨P, ?_⟩
  dsimp [IsTverbergPartition]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c y hy; rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩; exact (e i).2
  · intro i j hij; rw [Finset.disjoint_iff_ne]; rintro y1 hy1 y2 hy2 rfl
    rcases Finset.mem_image.mp hy1 with ⟨i1, hi1, rfl⟩
    rcases Finset.mem_image.mp hy2 with ⟨i2, hi2, heq⟩
    have heq_i : i1 = i2 := hx_inj heq.symm; subst heq_i
    have h1 : k i1 = i := (Finset.mem_filter.mp hi1).2
    have h2 : k i1 = j := (Finset.mem_filter.mp hi2).2
    have : i = j := h1.symm.trans h2
    exact hij this
  · ext y; constructor
    · intro hy; rcases Finset.mem_biUnion.mp hy with ⟨c, _, hc⟩
      rcases Finset.mem_image.mp hc with ⟨i, _, rfl⟩; exact (e i).2
    · intro hy; let s_elem : S := ⟨y, hy⟩; let i : Fin N := e.symm s_elem
      have hi_x : x i = y := by dsimp [x, i, s_elem]; rw [Equiv.apply_symm_apply]
      rw [Finset.mem_biUnion]; refine ⟨k i, Finset.mem_univ _, ?_⟩
      rw [Finset.mem_image]; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩, hi_x⟩
  · refine ⟨p, ?_⟩
    rw [Set.mem_iInter]; intro i; exact hp i

/-- **Radon's Lemma** (Tverberg's Theorem for r = 2):
Any set of d + 2 points in ℝ^d can be partitioned into 2 disjoint sets with intersecting convex hulls. -/
theorem radons_theorem
    (S : Finset (Fin d → ℝ)) (hS : S.card = (2 - 1) * (d + 1) + 1) :
    ∃ P : Fin 2 → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  classical
  let m := 1
  have hm : 1 ≤ m := by omega
  have hr_eq : 2 = m + 1 := rfl
  let e_r : Fin 2 ≃ Fin (m + 1) := finCongr hr_eq
  let N := m * (d + 1) + 1
  have hN_eq : N = (2 - 1) * (d + 1) + 1 := rfl
  have h_card : Fintype.card S = N := by rw [Fintype.card_coe, hS, hN_eq]
  let e : Fin N ≃ S := (Fintype.equivFinOfCardEq h_card).symm
  let x : Fin N → Fin d → ℝ := fun i ↦ (e i : Fin d → ℝ)
  have hx_inj : Function.Injective x := fun i1 i2 heq ↦ e.injective (Subtype.ext heq)
  let D := (d + 1) * m
  have hN : D + 1 ≤ N := by dsimp [D, N]; rw [mul_comm (d + 1) m]
  let matToVec : (Fin (d + 1) → Fin m → ℝ) → (Fin D → ℝ) :=
    fun M t ↦ M (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  have h_mat_inj : Function.Injective matToVec := by
    intro M1 M2 heq
    ext i j
    have ht := congr_fun heq (finProdFinEquiv (i, j))
    dsimp [matToVec] at ht
    rwa [Equiv.symm_apply_apply] at ht
  let v : Fin N → Fin 2 → (Fin D → ℝ) := fun i k ↦
    if k = 0 then matToVec (sarkariaLift m (x i) (Fin.last m))
    else - matToVec (sarkariaLift m (x i) (Fin.last m))
  have hv : ∀ i : Fin N, ∑ k : Fin 2, v i k = 0 := by
    intro i; rw [Fin.sum_univ_two]; dsimp [v]; ring
  obtain ⟨k2, w, hw_nonneg, hw_sum, h_zero_v⟩ := colorful_zero_sum_two D N hN v hv
  let k : Fin N → Fin (m + 1) := fun i ↦
    if k2 i = 0 then Fin.last m else Fin.castSucc ⟨0, hm⟩
  have h_zero_lift : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0 := by
    apply h_mat_inj; ext t
    have ht := congr_fun h_zero_v t
    dsimp [v, matToVec] at *; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at *
    have h_term : ∀ i ∈ Finset.univ,
        w i * sarkariaLift m (x i) (k i) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 =
        w i * (if k2 i = 0 then sarkariaLift m (x i) (Fin.last m) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
               else - sarkariaLift m (x i) (Fin.last m) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2) := by
      intro i _; dsimp [k]; split_ifs with hk0
      · rfl
      · dsimp [sarkariaLift]
        have h0_eq : (0 : Fin (m + 1)) = Fin.castSucc ⟨0, hm⟩ := rfl
        rw [h0_eq, auxVec_castSucc, auxVec_last]
        have h_eq_idx : (finProdFinEquiv.symm t).2 = ⟨0, hm⟩ := Subsingleton.elim _ _
        rw [h_eq_idx, Pi.single_eq_same]
        ring
    have h_split_if : (∑ i : Fin N, w i * (if k2 i = 0 then sarkariaLift m (x i) (Fin.last m) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
                                           else - sarkariaLift m (x i) (Fin.last m) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) =
                      (∑ i : Fin N, w i * (if k2 i = 0 then (fun t ↦ sarkariaLift m (x i) (Fin.last m) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
                                           else - (fun t ↦ sarkariaLift m (x i) (Fin.last m) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) t) := by
      apply Finset.sum_congr rfl; intro i _; split_ifs <;> rfl
    rw [Finset.sum_congr rfl h_term, h_split_if]; exact ht
  obtain ⟨P_m, hP_m⟩ := sarkaria_tverberg m S N (by rw [hS, hN_eq]) k w hw_nonneg hw_sum e h_zero_lift
  exact ⟨P_m, hP_m⟩

/-- **Trivial Tverberg's Theorem** (r = 1):
Any non-empty set S in ℝ^d can be partitioned into 1 set (itself) with non-empty convex hull. -/
theorem tverbergs_theorem_one
    (S : Finset (Fin d → ℝ)) (hS : S.card = (1 - 1) * (d + 1) + 1) :
    ∃ P : Fin 1 → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  classical
  refine ⟨fun _ ↦ S, ?_⟩
  dsimp [IsTverbergPartition]
  refine ⟨fun _ ↦ Subset.refl S, ?_, ?_, ?_⟩
  · intro i j hij; have : i = j := Subsingleton.elim i j; contradiction
  · ext x; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨fun ⟨_, hx⟩ ↦ hx, fun hx ↦ ⟨0, hx⟩⟩
  · have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hS_nonempty
    refine ⟨x, ?_⟩
    rw [Set.mem_iInter]; intro i; exact subset_convexHull ℝ (S : Set (Fin d → ℝ)) hx

/-- **Tverberg's Theorem** for r ≤ 2 (including Radon's Theorem for r = 2 and trivial partition for r = 1). -/
theorem tverbergs_theorem (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (S : Finset (Fin d → ℝ)) (hS : S.card = (r - 1) * (d + 1) + 1) :
    ∃ P : Fin r → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  rcases eq_or_lt_of_le hr1 with rfl | hr_gt
  · exact tverbergs_theorem_one S hS
  · have hr_two : r = 2 := by omega
    subst hr_two
    exact radons_theorem S hS

-- ============================================================================
-- Section 5: 1-Dimensional Tverberg Theorem for Arbitrary r (N = 2r - 1)
-- ============================================================================

/-- In 1 dimension (ℝ¹), any point between two endpoints lies in their convex hull. -/
lemma mem_convexHull_pair_1d (u v m : Fin 1 → ℝ) (h1 : u 0 ≤ m 0) (h2 : m 0 ≤ v 0) :
    m ∈ convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) := by
  by_cases huv : u 0 = v 0
  · have hu_eq_m : u = m := by
      ext ⟨i, hi⟩
      have : i = 0 := by omega
      subst this
      have : u 0 = m 0 := by linarith
      exact this
    have hm_in : m ∈ ({u, v} : Set (Fin 1 → ℝ)) := by
      rw [← hu_eq_m]
      exact Set.mem_insert u {v}
    exact subset_convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) hm_in
  · have huv_lt : u 0 < v 0 := lt_of_le_of_ne (le_trans h1 h2) huv
    have h_denom : 0 < v 0 - u 0 := by linarith
    let a := (v 0 - m 0) / (v 0 - u 0)
    let b := (m 0 - u 0) / (v 0 - u 0)
    have ha : 0 ≤ a := div_nonneg (by linarith) (le_of_lt h_denom)
    have hb : 0 ≤ b := div_nonneg (by linarith) (le_of_lt h_denom)
    have hab : a + b = 1 := by
      dsimp [a, b]
      rw [← add_div]
      have : v 0 - m 0 + (m 0 - u 0) = v 0 - u 0 := by ring
      rw [this, div_self (ne_of_gt h_denom)]
    have hm_comb : a • u + b • v = m := by
      ext ⟨i, hi⟩
      have : i = 0 := by omega
      subst this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [a, b]
      have : (v 0 - m 0) / (v 0 - u 0) * u 0 + (m 0 - u 0) / (v 0 - u 0) * v 0 = m 0 := by
        field_simp
        ring
      exact this
    have hu_conv : u ∈ convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) :=
      subset_convexHull ℝ _ (Set.mem_insert u {v})
    have hv_conv : v ∈ convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem u (Set.mem_singleton v))
    have h_conv := (convex_convexHull ℝ ({u, v} : Set (Fin 1 → ℝ))) hu_conv hv_conv ha hb hab
    rwa [hm_comb] at h_conv

/-- **1-Dimensional Tverberg Theorem for Arbitrary r (1966):**
    Any set S of 2r - 1 points in ℝ¹ can be partitioned into r subsets whose convex hulls
    share a common point of intersection. -/
theorem tverberg_1d (r : ℕ) (hr : 1 ≤ r)
    (S : Finset (Fin 1 → ℝ)) (hS : S.card = (r - 1) * (1 + 1) + 1) :
    ∃ P : Fin r → Finset (Fin 1 → ℝ), IsTverbergPartition S P := by
  rcases eq_or_lt_of_le hr with rfl | hr_gt
  · exact tverbergs_theorem_one S hS
  · rcases eq_or_lt_of_le (show 2 ≤ r by omega) with rfl | hr_gt2
    · exact radons_theorem S hS
    · have hr_le : r ≤ 2 ∨ 3 ≤ r := by omega
      rcases hr_le with hle | hge
      · exact tverbergs_theorem hr hle S hS
      · -- r ≥ 3 in 1D
        have hr_dim : (r - 1) * (1 + 1) + 1 = 2 * r - 1 := by omega
        classical
        let N := 2 * r - 1
        have hS_N : S.card = N := by
          dsimp [N]
          omega
        let coord : (Fin 1 → ℝ) → ℝ := fun x ↦ x 0
        have hcoord_inj : Function.Injective coord := by
          intro x y hxy
          funext i
          have hi : i = 0 := Subsingleton.elim i 0
          subst i
          exact hxy
        let T : Finset ℝ := S.image coord
        have hT_card : T.card = N := by
          dsimp [T]
          rw [Finset.card_image_of_injective S hcoord_inj, hS_N]
        let q : Fin N ↪o ℝ := T.orderEmbOfFin hT_card
        let x : Fin N → Fin 1 → ℝ := fun i _ ↦ q i
        have hx_inj : Function.Injective x := by
          intro i j hij
          apply q.injective
          exact congr_fun hij 0
        have hx_mem : ∀ i : Fin N, x i ∈ S := by
          intro i
          have hqi : q i ∈ T := by
            dsimp [q]
            exact T.orderEmbOfFin_mem hT_card i
          dsimp [T] at hqi
          rcases Finset.mem_image.mp hqi with ⟨y, hyS, hyq⟩
          have hxy : x i = y := by
            funext j
            have hj : j = 0 := Subsingleton.elim j 0
            subst j
            dsimp [x, coord] at hyq ⊢
            exact hyq.symm
          rw [hxy]
          exact hyS
        have hx_surj : ∀ y ∈ S, ∃ i : Fin N, x i = y := by
          intro y hyS
          have hyT : coord y ∈ T := by
            dsimp [T]
            exact Finset.mem_image.mpr ⟨y, hyS, rfl⟩
          have hq_image : Finset.image q Finset.univ = T := by
            dsimp [q]
            exact T.image_orderEmbOfFin_univ hT_card
          have hy_image : coord y ∈ Finset.image q Finset.univ := by
            rw [hq_image]
            exact hyT
          rcases Finset.mem_image.mp hy_image with ⟨i, _, hi⟩
          refine ⟨i, ?_⟩
          funext j
          have hj : j = 0 := Subsingleton.elim j 0
          subst j
          dsimp [x, coord] at hi ⊢
          exact hi
        have hmed : r - 1 < N := by
          dsimp [N]
          omega
        let med : Fin N := ⟨r - 1, hmed⟩
        let lower : Fin r → Fin N := fun c ↦
          ⟨c.1, by dsimp [N]; omega⟩
        let upper : Fin r → Fin N := fun c ↦
          ⟨2 * r - 2 - c.1, by dsimp [N]; omega⟩
        let I : Fin r → Finset (Fin N) := fun c ↦
          if c.1 = r - 1 then {med} else {lower c, upper c}
        let P : Fin r → Finset (Fin 1 → ℝ) := fun c ↦ (I c).image x
        have hI_unique : ∀ (i j : Fin r) (a : Fin N),
            a ∈ I i → a ∈ I j → i = j := by
          intro i j a hai haj
          by_cases hilast : i.1 = r - 1
          · by_cases hjlast : j.1 = r - 1
            · apply Fin.ext
              exact hilast.trans hjlast.symm
            · have hai' : a = med := by simpa [I, hilast] using hai
              have haj' : a = lower j ∨ a = upper j := by
                simpa [I, hjlast] using haj
              rcases haj' with haj' | haj'
              · have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [med, lower] at hv
                omega
              · have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [med, upper] at hv
                omega
          · by_cases hjlast : j.1 = r - 1
            · have hai' : a = lower i ∨ a = upper i := by
                simpa [I, hilast] using hai
              have haj' : a = med := by simpa [I, hjlast] using haj
              rcases hai' with hai' | hai'
              · have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [med, lower] at hv
                omega
              · have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [med, upper] at hv
                omega
            · have hai' : a = lower i ∨ a = upper i := by
                simpa [I, hilast] using hai
              have haj' : a = lower j ∨ a = upper j := by
                simpa [I, hjlast] using haj
              rcases hai' with hai' | hai' <;> rcases haj' with haj' | haj'
              · apply Fin.ext
                have hv := congr_arg Fin.val (hai'.symm.trans haj')
                simpa [lower] using hv
              · have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [lower, upper] at hv
                omega
              · have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [lower, upper] at hv
                omega
              · apply Fin.ext
                have hv := congr_arg Fin.val (hai'.symm.trans haj')
                dsimp [upper] at hv
                omega
        have hI_cover : ∀ a : Fin N, ∃ c : Fin r, a ∈ I c := by
          intro a
          by_cases halow : a.1 < r - 1
          · let c : Fin r := ⟨a.1, by omega⟩
            have hclast : c.1 ≠ r - 1 := by
              dsimp [c]
              omega
            refine ⟨c, ?_⟩
            rw [show I c = {lower c, upper c} by simp [I, hclast]]
            apply Finset.mem_insert.mpr
            left
            apply Fin.ext
            rfl
          · by_cases hamid : a.1 = r - 1
            · let c : Fin r := ⟨r - 1, by omega⟩
              have hclast : c.1 = r - 1 := by rfl
              refine ⟨c, ?_⟩
              rw [show I c = {med} by simp [I, hclast]]
              apply Finset.mem_singleton.mpr
              apply Fin.ext
              exact hamid
            · have ha_lt : a.1 < 2 * r - 1 := a.2
              let c : Fin r := ⟨2 * r - 2 - a.1, by omega⟩
              have hclast : c.1 ≠ r - 1 := by
                dsimp [c]
                omega
              refine ⟨c, ?_⟩
              rw [show I c = {lower c, upper c} by simp [I, hclast]]
              apply Finset.mem_insert.mpr
              right
              apply Finset.mem_singleton.mpr
              apply Fin.ext
              dsimp [upper, c, N] at a ⊢
              omega
        refine ⟨P, ?_⟩
        dsimp [IsTverbergPartition]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro c y hy
          rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
          exact hx_mem i
        · intro i j hij
          rw [Finset.disjoint_iff_ne]
          rintro y₁ hy₁ y₂ hy₂ heq
          rcases Finset.mem_image.mp hy₁ with ⟨a, ha, rfl⟩
          rcases Finset.mem_image.mp hy₂ with ⟨b, hb, rfl⟩
          have hab' : a = b := hx_inj heq
          subst b
          exact hij (hI_unique i j a ha hb)
        · ext y
          constructor
          · intro hy
            rcases Finset.mem_biUnion.mp hy with ⟨c, _, hyc⟩
            rcases Finset.mem_image.mp hyc with ⟨i, _, rfl⟩
            exact hx_mem i
          · intro hy
            rcases hx_surj y hy with ⟨i, rfl⟩
            rcases hI_cover i with ⟨c, hic⟩
            exact Finset.mem_biUnion.mpr
              ⟨c, Finset.mem_univ c, Finset.mem_image.mpr ⟨i, hic, rfl⟩⟩
        · refine ⟨x med, ?_⟩
          rw [Set.mem_iInter]
          intro c
          by_cases hclast : c.1 = r - 1
          · apply subset_convexHull ℝ (P c : Set (Fin 1 → ℝ))
            exact Finset.mem_coe.mpr <| Finset.mem_image.mpr ⟨med, by simp [I, hclast], rfl⟩
          · have hc_lt : c.1 < r - 1 := by omega
            have hlo : x (lower c) 0 ≤ x med 0 := by
              change q (lower c) ≤ q med
              apply q.monotone
              change c.1 ≤ r - 1
              omega
            have hhi : x med 0 ≤ x (upper c) 0 := by
              change q med ≤ q (upper c)
              apply q.monotone
              change r - 1 ≤ 2 * r - 2 - c.1
              omega
            simpa [P, I, hclast] using
              (mem_convexHull_pair_1d (x (lower c)) (x (upper c)) (x med) hlo hhi)

end TverbergsTheorem

#print axioms TverbergsTheorem.radons_theorem
#print axioms TverbergsTheorem.tverbergs_theorem
#print axioms TverbergsTheorem.sarkaria_tverberg
#print axioms TverbergsTheorem.mem_convexHull_pair_1d
#print axioms TverbergsTheorem.tverberg_1d

