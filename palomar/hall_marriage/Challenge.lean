import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Fintype.Basic

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

/-- **Hall's Marriage Theorem (Sufficiency / Equivalence, Freek Wiedijk #87):**
A finite collection of sets admits a system of distinct representatives if and only if
it satisfies Hall's condition. -/
theorem hall_marriage_theorem (A : ι → Finset α) :
    (∃ f : ι → α, IsSDR A f) ↔ HallCondition A := sorry

end HallMarriage
