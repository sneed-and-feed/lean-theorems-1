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
# Auxiliary Basis and Affine Coordinates for Tverberg's Theorem

This module defines the zero-sum auxiliary basis vectors, lifted affine coordinates,
and the fundamental Tverberg partition predicate.

## Main Definitions
* `auxVec`: Standard auxiliary basis vectors in $\mathbb{R}^m$ with zero sum.
* `liftAffine`: Lifted point in affine space $\mathbb{R}^{d+1}$ ($x \mapsto (x, 1)$).
* `IsTverbergPartition`: Predicate defining a valid Tverberg partition of a point set.
* `IsTverbergPartition.extend_superset`: Extension of a Tverberg partition to a superset.

## References
* H. Tverberg (1966), *A generalization of Radon's theorem*, J. London Math. Soc. 41:123–128.
* K. S. Sarkaria (1992), *A generalized van Kampen-Flores theorem*, Proc. Amer. Math. Soc. 115:339–346.
-/

set_option linter.deprecated false

namespace TverbergsTheorem

open Finset BigOperators

variable {d r : ℕ}

/-- Standard auxiliary basis vectors in ℝ^m with zero sum. -/
def auxVec (m : ℕ) (k : Fin (m + 1)) : Fin m → ℝ :=
  if h : k.1 < m then Pi.single ⟨k.1, h⟩ 1 else fun _ ↦ -1

lemma auxVec_castSucc (m : ℕ) (j : Fin m) : auxVec m (Fin.castSucc j) = Pi.single j 1 := by
  dsimp [auxVec]; split_ifs with h <;> [congr; omega]

lemma auxVec_last (m : ℕ) : auxVec m (Fin.last m) = fun _ ↦ -1 := by
  dsimp [auxVec]; split_ifs with h <;> [omega; rfl]

lemma sum_auxVec_zero (m : ℕ) : ∑ k : Fin (m + 1), auxVec m (k : Fin (m + 1)) = (0 : Fin m → ℝ) := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [auxVec_castSucc, auxVec_last]
  ext j
  simp [Finset.sum_pi_single j (fun _ ↦ (1 : ℝ))]

/-- Lifted point in affine space ℝ^{d+1}. -/
def liftAffine (x : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc x 1

lemma liftAffine_last (x : Fin d → ℝ) : liftAffine x (Fin.last d) = 1 := by simp [liftAffine]
lemma liftAffine_castSucc (x : Fin d → ℝ) (t : Fin d) : liftAffine x (Fin.castSucc t) = x t := by simp [liftAffine]

/-- **Tverberg's Partition Property:**
A collection of `r` pairwise disjoint subsets of `S` that partition `S`
and whose convex hulls have a non-empty intersection. -/
def IsTverbergPartition (S : Finset (Fin d → ℝ)) (P : Fin r → Finset (Fin d → ℝ)) : Prop :=
  (∀ i, P i ⊆ S) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  (Finset.biUnion Finset.univ P = S) ∧
  (⋂ i : Fin r, convexHull ℝ (P i : Set (Fin d → ℝ))).Nonempty

/-- A Tverberg partition of a subset extends to the whole finite set: assign every
new point to one distinguished block. Enlarging that block preserves the common
point of the convex hulls. -/
lemma IsTverbergPartition.extend_superset (hr : 1 ≤ r)
    {T S : Finset (Fin d → ℝ)} {P : Fin r → Finset (Fin d → ℝ)}
    (hTS : T ⊆ S) (hP : IsTverbergPartition T P) :
    ∃ Q : Fin r → Finset (Fin d → ℝ), IsTverbergPartition S Q := by
  classical
  rcases hP with ⟨hP_sub, hP_disj, hP_cov, ⟨x, hx⟩⟩
  let i₀ : Fin r := ⟨0, hr⟩
  let Q : Fin r → Finset (Fin d → ℝ) := fun i ↦ if i = i₀ then P i ∪ (S \ T) else P i
  have hPQ : ∀ i, P i ⊆ Q i := fun i y hy ↦ by
    by_cases hi : i = i₀
    · subst hi; exact Finset.mem_union_left _ hy
    · simpa [Q, hi] using hy
  have hQS : ∀ i, Q i ⊆ S := by
    intro i y hy
    by_cases hi : i = i₀
    · subst hi; simp only [Q, ite_true, mem_union, mem_sdiff] at hy
      exact hy.elim (fun h ↦ hTS (hP_sub i₀ h)) And.left
    · simp only [Q, hi, ite_false] at hy; exact hTS (hP_sub i hy)
  have hQ_disj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j) := by
    intro i j hij
    rw [Finset.disjoint_iff_ne]
    rintro u hu v hv rfl
    by_cases hi : i = i₀
    · subst hi
      have hj : j ≠ i₀ := hij.symm
      simp only [Q, ite_true, hj, ite_false, mem_union, mem_sdiff] at hu hv
      rcases hu with hu | ⟨_, hu⟩
      · exact Finset.disjoint_left.mp (hP_disj i₀ j hij) hu hv
      · exact hu (hP_sub j hv)
    · by_cases hj : j = i₀
      · subst hj
        simp only [Q, hi, ite_true, ite_false, mem_union, mem_sdiff] at hu hv
        rcases hv with hv | ⟨_, hv⟩
        · exact Finset.disjoint_left.mp (hP_disj i i₀ hij) hu hv
        · exact hv (hP_sub i hu)
      · simp only [Q, hi, hj, ite_false] at hu hv
        exact Finset.disjoint_left.mp (hP_disj i j hij) hu hv
  have hQ_cov : Finset.biUnion Finset.univ Q = S := by
    ext y; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨fun ⟨i, hy⟩ ↦ hQS i hy, fun hy ↦ ?_⟩
    by_cases hyT : y ∈ T
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hP_cov ▸ hyT)
      exact ⟨i, hPQ i hi⟩
    · exact ⟨i₀, by simp [Q, Finset.mem_sdiff.mpr ⟨hy, hyT⟩]⟩
  refine ⟨Q, hQS, hQ_disj, hQ_cov, ⟨x, Set.mem_iInter.mpr fun i ↦
    convexHull_mono (fun _ hy ↦ hPQ i hy) (Set.mem_iInter.mp hx i)⟩⟩

end TverbergsTheorem
