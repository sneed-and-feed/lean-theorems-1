import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset

/-- **Bollobás's Two Families Theorem (1965)**:
Let $(A_i)_{i=1}^m$ and $(B_i)_{i=1}^m$ be two families of finite sets such that $A_i \cap B_i = \emptyset$
for all $i$, and $A_i \cap B_j \neq \emptyset$ for all $i \neq j$.
Then $\sum_{i=1}^m \frac{1}{\binom{|A_i| + |B_i|}{|A_i|}} \le 1$. -/
theorem bollobas_two_families {α : Type*} [DecidableEq α] {m : ℕ}
    (A B : Fin m → Finset α)
    (h_disj : ∀ i, Disjoint (A i) (B i))
    (h_inter : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i : Fin m, (1 : ℝ) / ((A i).card + (B i).card).choose (A i).card ≤ 1 := sorry

/-- **Uniform Bollobás Two Families Theorem (1965)**:
If $|A_i| = a$ and $|B_i| = b$ for all $i$, then $m \le \binom{a+b}{a}$. -/
theorem bollobas_uniform {α : Type*} [DecidableEq α] {m a b : ℕ}
    (A B : Fin m → Finset α)
    (h_disj : ∀ i, Disjoint (A i) (B i))
    (h_inter : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j))
    (hA : ∀ i, (A i).card = a)
    (hB : ∀ i, (B i).card = b) :
    (m : ℝ) ≤ (Nat.choose (a + b) a : ℝ) := sorry