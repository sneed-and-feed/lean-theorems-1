import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic

/-!
# Radon's Lemma and Helly's Theorem (Freek Wiedijk #99)

This module provides the formalization stub for **Radon's Lemma (Radon's Theorem)** (J. Radon, 1921)
and **Helly's Theorem on Convex Sets** (E. Helly, 1923).

## Mathematical Statements

1. **Radon's Lemma / Theorem (1921):**
   Any set of $d + 2$ points in $\mathbb{R}^d$ can be partitioned into two disjoint subsets
   $A$ and $B$ whose convex hulls intersect:
   $$A \cap B = \emptyset, \quad \operatorname{conv}(A) \cap \operatorname{conv}(B) \ne \emptyset$$

2. **Helly's Theorem (1923):**
   Let $C_1, \dots, C_n$ be a finite collection of convex sets in $\mathbb{R}^d$ with $n \ge d + 1$.
   If every subcollection of $d + 1$ sets has a non-empty intersection, then the entire collection
   has a non-empty intersection:
   $$\bigcap_{i=1}^n C_i \ne \emptyset$$

## References
* J. Radon (1921), *Mengen konvexer Körper, die einen gemeinsamen Punkt enthalten*, Math. Ann., 83(1-2):113–115.
* E. Helly (1923), *Über Mengen konvexer Körper mit gemeinschaftlichen Punkten*, Jahresber. Deutsch. Math.-Verein., 32:175–176.
* F. Wiedijk (2008), *Formalizing 100 Theorems*, #99.
-/

namespace RadonHelly

open Finset

variable {d : ℕ}

/-- **Radon's Lemma / Theorem (1921):**
Any collection of `d + 2` points in `Fin d → ℝ` can be partitioned into two disjoint subsets
whose convex hulls intersect. -/
theorem radons_theorem (S : Finset (Fin d → ℝ)) (hS : S.card = d + 2) :
    ∃ A B : Finset (Fin d → ℝ), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ A ∪ B = S ∧
      (convexHull ℝ (A : Set (Fin d → ℝ)) ∩ convexHull ℝ (B : Set (Fin d → ℝ))).Nonempty := by
  sorry

/-- **Helly's Theorem for Finite Families of Convex Sets (1923, Freek Wiedijk #99):**
If `C` is a finite family of convex subsets in `Fin d → ℝ` such that every subfamily of size `d + 1`
has non-empty intersection, then the entire family has non-empty intersection. -/
theorem hellys_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → Set (Fin d → ℝ))
    (h_convex : ∀ i : ι, Convex ℝ (C i))
    (h_inter : ∀ J : Finset ι, J.card ≤ d + 1 → (⋂ i ∈ J, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty := by
  sorry

end RadonHelly
