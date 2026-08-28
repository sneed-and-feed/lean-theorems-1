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
If `C` is a finite family of convex subsets in `Fin d → ℝ` such that every subfamily of size
at most `d + 1` (`J.card ≤ d + 1`) has non-empty intersection, then the entire family has
non-empty intersection.

### Small-Family Scope and Equivalence
- **Boundary / Small Families (`|ι| ≤ d + 1`)**: For families with `|ι| ≤ d + 1`, choosing
  `J = Finset.univ` satisfies `J.card ≤ d + 1`, so the hypothesis directly entails that the entire
  family has non-empty intersection. The `≤ d + 1` hypothesis avoids the vacuous-truth failure of
  the exact-size `= d + 1` condition when `|ι| ≤ d`.
- **Large Families (`|ι| > d + 1`)**: When `|ι| > d + 1`, any subfamily of size `≤ d + 1` can be
  extended to a subfamily of size `d + 1`, so the `≤ d + 1` condition is equivalent to the classical
  statement requiring every `(d + 1)`-element subfamily to intersect. -/
theorem hellys_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → Set (Fin d → ℝ))
    (h_convex : ∀ i : ι, Convex ℝ (C i))
    (h_inter : ∀ J : Finset ι, J.card ≤ d + 1 → (⋂ i ∈ J, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty := sorry

end RadonHelly
