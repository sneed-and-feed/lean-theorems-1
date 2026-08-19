import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset

/-- A complete bipartite decomposition of K_n is given by a family of pairs of disjoint subsets
    (L_k, R_k) such that every distinct pair of vertices {u, v} is covered by exactly one bipartite graph. -/
def IsCompleteBipartitePartition (n m : ℕ) (L R : Fin m → Finset (Fin n)) : Prop :=
  (∀ k, Disjoint (L k) (R k)) ∧
  (∀ u v : Fin n, u ≠ v →
    ∃! k : Fin m, (u ∈ L k ∧ v ∈ R k) ∨ (u ∈ R k ∧ v ∈ L k))

lemma sum_sq_identity (n : ℕ) (x : Fin n → ℝ) :
    (∑ i : Fin n, x i) ^ 2 = ∑ i : Fin n, (x i) ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0 := by
  have h_sq : (∑ i : Fin n, x i) ^ 2 = (∑ i : Fin n, x i) * (∑ j : Fin n, x j) := sq (∑ i, x i)
  rw [h_sq, Fintype.sum_mul_sum]
  have h_split : (∑ i : Fin n, ∑ j : Fin n, x i * x j) =
      (∑ i : Fin n, ∑ j : Fin n, ((if i = j then x i * x j else 0) +
        (if i < j then x i * x j else 0) + (if j < i then x i * x j else 0))) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with hij | rfl | hji
    · have h1 : ¬ (i = j) := ne_of_lt hij
      have h2 : ¬ (j < i) := not_lt_of_gt hij
      simp [hij, h1, h2]
    · have h1 : ¬ (i < i) := lt_irrefl i
      simp [h1]
    · have h1 : ¬ (i = j) := ne_of_gt hji
      have h2 : ¬ (i < j) := not_lt_of_gt hji
      simp [hji, h1, h2]
  rw [h_split]
  simp only [sum_add_distrib]
  have h_diag : (∑ i : Fin n, ∑ j : Fin n, if i = j then x i * x j else 0) = ∑ i : Fin n, (x i) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    simp [sq]
  have h_symm : (∑ i : Fin n, ∑ j : Fin n, if j < i then x i * x j else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm]
  rw [h_diag, h_symm]
  ring

/-- Sub-lemma 2: Bipartite edge sum equals product sum. -/
lemma bipartite_sum_eq (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) =
      ∑ k : Fin m, (∑ i ∈ L k, x i) * (∑ j ∈ R k, x j) := by
  sorry

/-- Main Theorem: Graham-Pollak Theorem (1971 / Tverberg 1982). -/
theorem graham_pollak (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) :
    n - 1 ≤ m := by
  sorry
