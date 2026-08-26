import Mathlib.Data.Finset.Basic
import Mathlib.Order.Antichain

namespace DilworthTheorem

variable {α : Type*} [DecidableEq α] [PartialOrder α]

/-- A subset of `α` is a chain if every two elements are comparable. -/
def IsChain (s : Set α) : Prop :=
  ∀ x y, x ∈ s → y ∈ s → x ≤ y ∨ y ≤ x

/-- A subset of `α` is an antichain if no two distinct elements are comparable. -/
def IsAntichain (s : Set α) : Prop :=
  ∀ x y, x ∈ s → y ∈ s → x ≠ y → ¬(x ≤ y) ∧ ¬(y ≤ x)

/-- A chain partition / cover of a finset `S` into `k` chains. -/
def IsChainCover (S : Finset α) {k : ℕ} (C : Fin k → Finset α) : Prop :=
  (∀ i, IsChain (C i : Set α)) ∧
  (Finset.biUnion Finset.univ C = S) ∧
  (∀ i j, i ≠ j → Disjoint (C i) (C j))

/-- An antichain partition / cover of a finset `S` into `k` antichains. -/
def IsAntichainCover (S : Finset α) {k : ℕ} (A : Fin k → Finset α) : Prop :=
  (∀ i, IsAntichain (A i : Set α)) ∧
  (Finset.biUnion Finset.univ A = S) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j))

/-- **Dilworth's Theorem (R. P. Dilworth, 1950):**
If every antichain in a finite poset `S` has size at most `k`, then `S` can be partitioned
into `k` chains. -/
theorem dilworth_theorem (S : Finset α) (k : ℕ)
    (h_anti : ∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) :
    ∃ C : Fin k → Finset α, IsChainCover S C := sorry

/-- **Mirsky's Theorem (Dual Dilworth Theorem, L. Mirsky, 1971):**
If every chain in a finite poset `S` has size at most `m`, then `S` can be partitioned
into `m` antichains. -/
theorem mirsky_theorem (S : Finset α) (m : ℕ)
    (h_chain : ∀ C ⊆ S, IsChain (C : Set α) → C.card ≤ m) :
    ∃ A : Fin m → Finset α, IsAntichainCover S A := sorry

end DilworthTheorem
