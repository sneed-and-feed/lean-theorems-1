import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Erdős–Ko–Rado Theorem (1961):**
Let `α` be a finite type of size `n` with `n ≥ 2k` and `k ≥ 1`.
If `ℱ` is an intersecting family of `k`-element subsets of `α`, then
`|ℱ| ≤ Nat.choose (n - 1) (k - 1)`. -/
theorem erdos_ko_rado {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) :
    F.card ≤ Nat.choose (n - 1) (k - 1) := sorry

/-- A family `F` of sets is a star (canonically centered) if all sets share a common element `x`. -/
def IsStarFamily (F : Finset (Finset α)) : Prop :=
  ∃ x : α, ∀ A ∈ F, x ∈ A

/-- The Hilton–Milner extremal bound: $\binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$. -/
def hiltonMilnerBound (n k : ℕ) : ℕ :=
  Nat.choose (n - 1) (k - 1) - Nat.choose (n - k - 1) (k - 1) + 1

/-- **Sharpness of the Hilton–Milner Bound (1967):**
For every `2 ≤ k` and `2k < n`, there exists a uniform, pairwise-intersecting, non-star family
whose cardinality is exactly `hiltonMilnerBound n k`. -/
theorem exists_hiltonMilner_extremizer {n k : ℕ} (hn : Fintype.card α = n)
    (hk : 2 ≤ k) (h2k : 2 * k < n) :
    ∃ F : Finset (Finset α),
      (∀ A ∈ F, A.card = k) ∧
      (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
      ¬ IsStarFamily F ∧
      F.card = hiltonMilnerBound n k := sorry