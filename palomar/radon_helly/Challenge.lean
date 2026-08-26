import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

namespace RadonHelly

variable {d : ℕ}

/-- **Radon's Lemma (Radon's Theorem, 1921, Freek Wiedijk #99):**
Any set of $d + 2$ points in $\mathbb{R}^d$ can be partitioned into two disjoint subsets
whose convex hulls intersect. -/
theorem radons_theorem (S : Finset (Fin d → ℝ)) (hS : S.card = d + 2) :
    ∃ A B : Finset (Fin d → ℝ), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ A ∪ B = S ∧
      (convexHull ℝ (A : Set (Fin d → ℝ)) ∩ convexHull ℝ (B : Set (Fin d → ℝ))).Nonempty := sorry

/-- **Helly's Theorem for Finite Families of Convex Sets (1923, Freek Wiedijk #99):**
If `C` is a finite family of convex subsets in `Fin d → ℝ` such that every subfamily of size `d + 1`
has non-empty intersection, then the entire family has non-empty intersection. -/
theorem hellys_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → Set (Fin d → ℝ))
    (h_convex : ∀ i : ι, Convex ℝ (C i))
    (h_inter : ∀ J : Finset ι, J.card ≤ d + 1 → (⋂ i ∈ J, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty := sorry

end RadonHelly
