import Formalization.TverbergsTheorem.Basis
import Formalization.TverbergsTheorem.Sarkaria
import Formalization.ColorfulCaratheodory
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace TverbergsTheorem

/-- Any point in the convex hull of the range of a finite family can be represented
as an authentic convex combination with non-negative weights summing to 1. -/
lemma exists_weights_of_mem_convexHull_range {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) (x : E)
    (hx : x ∈ convexHull ℝ (Set.range v)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∑ i, w i • v i = x) := by
  rw [convexHull_range_eq_exists_affineCombination] at hx
  rcases hx with ⟨s, w, hw0, hw1, haff⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1] at haff
  let w' : ι → ℝ := fun i ↦ if i ∈ s then w i else 0
  refine ⟨w', fun i ↦ by dsimp [w']; split_ifs with hi <;> [exact hw0 i hi; rfl],
    by dsimp [w']; rw [Finset.sum_ite_mem_eq, hw1],
    by dsimp [w']; simp_rw [ite_smul, zero_smul, Finset.sum_ite_mem_eq, haff]⟩

/-- If a finite family of m + 1 vectors sums to 0, then 0 lies in the convex hull
of its range (witnessed by the center of mass with uniform weights). -/
lemma zero_mem_convexHull_of_sum_zero (m : ℕ) {E : Type*} [AddCommGroup E] [Module ℝ E] (z : Fin (m + 1) → E)
    (hz_zero : ∑ k : Fin (m + 1), z k = 0) :
    (0 : E) ∈ convexHull ℝ (Set.range z) := by
  have h_cm : (Finset.univ : Finset (Fin (m + 1))).centerMass (fun _ ↦ (1 : ℝ)) z = 0 := by
    dsimp [Finset.centerMass]; simp [hz_zero]
  rw [← h_cm]
  exact Finset.centerMass_mem_convexHull Finset.univ (fun _ _ ↦ by positivity) (by simp; positivity)
    (fun k _ ↦ Set.mem_range_self k)

/-- Reindexing a Tverberg partition along an equivalence preserves the Tverberg partition property. -/
lemma isTverbergPartition_reindex {d r₁ r₂ : ℕ} (e : Fin r₁ ≃ Fin r₂)
    {S : Finset (Fin d → ℝ)} {P : Fin r₂ → Finset (Fin d → ℝ)}
    (hP : IsTverbergPartition S P) :
    IsTverbergPartition S (fun i ↦ P (e i)) := by
  rcases hP with ⟨hsub, hdisj, hcov, ⟨x, hx⟩⟩
  refine ⟨fun i ↦ hsub (e i), fun i j hij ↦ hdisj (e i) (e j) (fun he ↦ hij (e.injective he)), ?_,
    ⟨x, Set.mem_iInter.2 fun i ↦ Set.mem_iInter.1 hx (e i)⟩⟩
  ext y
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rw [← hcov]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨e i, hi⟩, fun ⟨j, hj⟩ ↦ ⟨e.symm j, by simpa using hj⟩⟩

/-- **The Colorful Carathéodory – Sarkaria Bridge**:
For any dimension d and any number of parts r ≥ 2, any set S of (r - 1) * (d + 1) + 1 points
in ℝ^d admits a valid Tverberg partition into r parts whose convex hulls intersect.
The proof applies Bárány's Colorful Carathéodory theorem to the D + 1 color classes
formed by Sarkaria tensor liftings in dimension D = (d + 1) * (r - 1), extracting a
zero-sum convex combination that feeds directly into Sarkaria's reduction. -/
theorem tverberg_bridge {d r : ℕ} (hr : 2 ≤ r)
    (S : Finset (Fin d → ℝ)) (hS : S.card = (r - 1) * (d + 1) + 1) :
    ∃ P : Fin r → Finset (Fin d → ℝ), IsTverbergPartition S P := by
  classical
  let m := r - 1
  let D := (d + 1) * m
  let N := D + 1
  have hN_eq : S.card = N := by dsimp [N, D, m]; rw [hS, mul_comm]
  have h_card : Fintype.card S = N := by rw [Fintype.card_coe, hN_eq]
  let e : Fin N ≃ S := (Fintype.equivFinOfCardEq h_card).symm
  let x : Fin N → Fin d → ℝ := fun i ↦ (e i : Fin d → ℝ)
  let matToVec : (Fin (d + 1) → Fin m → ℝ) → (Fin D → ℝ) :=
    fun M t ↦ M (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  have h_mat_inj : Function.Injective matToVec := fun M1 M2 heq ↦ by
    ext i j; have ht := congr_fun heq (finProdFinEquiv (i, j))
    dsimp [matToVec] at ht; rwa [Equiv.symm_apply_apply] at ht
  have h_mat_zero : matToVec (0 : Fin (d + 1) → Fin m → ℝ) = 0 := rfl
  have h_mat_sum_m (M : Fin (m + 1) → Fin (d + 1) → Fin m → ℝ) :
      matToVec (∑ k, M k) = ∑ k, matToVec (M k) := by
    ext t; simp [matToVec, Finset.sum_apply]
  have h_mat_sum_smul (w : Fin N → ℝ) (M : Fin N → Fin (d + 1) → Fin m → ℝ) :
      matToVec (∑ i, w i • M i) = ∑ i, w i • matToVec (M i) := by
    ext t; simp [matToVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let V : Fin (D + 1) → Set (Fin D → ℝ) :=
    fun i ↦ Set.range (fun k : Fin (m + 1) ↦ matToVec (sarkariaLift m (x i) k))
  have h_zero_V (i : Fin (D + 1)) : (0 : Fin D → ℝ) ∈ convexHull ℝ (V i) := by
    apply zero_mem_convexHull_of_sum_zero m
    rw [← h_mat_sum_m, sum_sarkariaLift_zero, h_mat_zero]
  obtain ⟨f, hf_col, hf_origin⟩ := ColorfulCaratheodory.colorful_caratheodory_origin V h_zero_V
  choose k hk using fun i ↦ Set.mem_range.mp (hf_col i)
  obtain ⟨w, hw_nonneg, hw_sum, hw_comb⟩ := exists_weights_of_mem_convexHull_range f 0 hf_origin
  have h_zero_lift : (∑ i : Fin N, w i • sarkariaLift m (x i) (k i)) = 0 := by
    apply h_mat_inj
    rw [h_mat_sum_smul, Finset.sum_congr rfl (fun i _ ↦ by rw [hk i]), hw_comb, h_mat_zero]
  obtain ⟨P_m, hP_m⟩ := sarkaria_tverberg m S N hN_eq k w hw_nonneg hw_sum e h_zero_lift
  have hm_eq : m + 1 = r := by omega
  let e_r : Fin r ≃ Fin (m + 1) := (finCongr hm_eq).symm
  exact ⟨fun i ↦ P_m (e_r i), isTverbergPartition_reindex e_r hP_m⟩

end TverbergsTheorem
