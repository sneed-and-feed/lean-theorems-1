import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Hall's Marriage Theorem (Freek Wiedijk #87)

This module provides the formalization stub for **Hall's Marriage Theorem** /
Hall's Marriage Condition on Systems of Distinct Representatives (P. Hall, 1935).

## Mathematical Statement
Let $A_1, \dots, A_n$ be a finite family of finite sets indexed by a finite type $\iota$.
A **System of Distinct Representatives (SDR)** (or transversal) is an injective choice function
$f : \iota \to \alpha$ such that $\forall i \in \iota, f(i) \in A_i$.

**Hall's Theorem:** A system of distinct representatives exists if and only if **Hall's Marriage Condition**
holds: for every subset of indices $J \subseteq \iota$,
$$\left| \bigcup_{i \in J} A_i \right| \ge |J|$$

## References
* P. Hall (1935), *On Representatives of Subsets*, J. London Math. Soc., 10(1):26–30.
* P. R. Halmos & H. E. Vaughan (1950), *The Marriage Problem*, Amer. J. Math., 72(1):214–215.
* F. Wiedijk (2008), *Formalizing 100 Theorems*, #87.
-/

namespace HallMarriage

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι]

/-- Hall's marriage condition: for every subset of indices `J`, the union of sets `A i` for `i ∈ J`
has cardinality at least `|J|`. -/
def HallCondition (A : ι → Finset α) : Prop :=
  ∀ J : Finset ι, J.card ≤ (J.biUnion A).card

/-- A System of Distinct Representatives (SDR) / Transversal for the indexed family `A`. -/
def IsSDR (A : ι → Finset α) (f : ι → α) : Prop :=
  Function.Injective f ∧ ∀ i : ι, f i ∈ A i

/-- **Hall's Marriage Theorem (Necessity):**
If a system of distinct representatives exists, then Hall's condition holds. -/
theorem hall_marriage_necessary (A : ι → Finset α) (f : ι → α) (hf : IsSDR A f) :
    HallCondition A := by
  sorry

/-- **Hall's Marriage Theorem (Sufficiency / Equivalence, Freek Wiedijk #87):**
A finite collection of sets admits a system of distinct representatives if and only if
it satisfies Hall's condition. -/
theorem hall_marriage_theorem (A : ι → Finset α) :
    (∃ f : ι → α, IsSDR A f) ↔ HallCondition A := by
  sorry

end HallMarriage
