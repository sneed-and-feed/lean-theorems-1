import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

namespace TverbergsTheorem

variable {d r : ℕ}

/-- **Tverberg's Partition Property:**
A collection of `r` pairwise disjoint subsets of `S` that partition `S`
and whose convex hulls have a non-empty intersection. -/
def IsTverbergPartition (S : Finset (Fin d → ℝ)) (P : Fin r → Finset (Fin d → ℝ)) : Prop :=
  (∀ i, P i ⊆ S) ∧
  (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
  (Finset.biUnion Finset.univ P = S) ∧
  (⋂ i : Fin r, convexHull ℝ (P i : Set (Fin d → ℝ))).Nonempty

/-- **Tverberg's Theorem** for r ≤ 2 (including Radon's Theorem for r = 2 and trivial partition for r = 1). -/
theorem tverbergs_theorem (hr1 : 1 ≤ r) (hr2 : r ≤ 2)
    (S : Finset (Fin d → ℝ)) (hS : S.card = (r - 1) * (d + 1) + 1) :
    ∃ P : Fin r → Finset (Fin d → ℝ), IsTverbergPartition S P := sorry

/-- **1-Dimensional Tverberg Theorem for Arbitrary r (1966):**
Any set S of 2r - 1 points in ℝ¹ can be partitioned into r subsets whose convex hulls
share a common point of intersection. -/
theorem tverberg_1d (r : ℕ) (hr : 1 ≤ r)
    (S : Finset (Fin 1 → ℝ)) (hS : S.card = (r - 1) * (1 + 1) + 1) :
    ∃ P : Fin r → Finset (Fin 1 → ℝ), IsTverbergPartition S P := sorry

/-- **1-Dimensional Colorful Tverberg Theorem for Arbitrary r (Bárány–Larman–Pach 1992 / d = 1)**:
Given two disjoint color classes of r points each in ℝ¹, they can be partitioned into r disjoint
colorful pairs (each containing 1 point from C₀ and 1 point from C₁) whose convex hulls share
a common point of intersection. -/
theorem colorful_tverberg_1d (r : ℕ) (hr : 1 ≤ r)
    (C₀ C₁ : Finset (Fin 1 → ℝ)) (h₀ : C₀.card = r) (h₁ : C₁.card = r)
    (h_disj : Disjoint C₀ C₁) :
    ∃ P : Fin r → Finset (Fin 1 → ℝ),
      (∀ i, (P i).card = 2) ∧
      (∀ i, ∃ x ∈ C₀, ∃ y ∈ C₁, P i = {x, y}) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (Finset.biUnion Finset.univ P = C₀ ∪ C₁) ∧
      (⋂ i : Fin r, convexHull ℝ (P i : Set (Fin 1 → ℝ))).Nonempty := sorry

end TverbergsTheorem
