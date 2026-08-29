import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Formalization.GilmerUnionClosed.Basic
import Formalization.GilmerUnionClosed.GoldenRatio

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GilmerUnionClosed

/-!
# Certified Concrete Union-Closed Families and Frequencies

This module constructs and certifies canonical union-closed families:
- Two-element pairs $\{\emptyset, \{a\}\}$: union-closed with element frequency exactly $1/2 \ge c_0$.
- Singletons $\{\{a\}\}$: union-closed with element frequency 1.
- Chain families: totally ordered by inclusion, closed under unions.
- Powerset families $\mathcal{P}(S)$: fiber bijections, element frequency exactly $1/2 \ge c_0$,
  and Frankl/Gilmer certificates for all non-empty finite sets.
-/

section ConcreteFamilies

variable {α : Type*} [DecidableEq α]

/-- The canonical two-element union-closed family $\{\emptyset, \{a\}\}$. -/
def pairEmptySingleton (a : α) : Finset (Finset α) := {∅, {a}}

/-- The singleton union-closed family $\{\{a\}\}$. -/
def singletonFamily (a : α) : Finset (Finset α) := {{a}}

/-- The card of $\{\emptyset, \{a\}\}$ is 2. -/
theorem pairEmptySingleton_card (a : α) : (pairEmptySingleton a).card = 2 :=
  Finset.card_pair (Finset.singleton_ne_empty a).symm

/-- The family $\{\emptyset, \{a\}\}$ is union-closed. -/
theorem pairEmptySingleton_isUnionClosed (a : α) :
    IsUnionClosed (pairEmptySingleton a) := by
  simp [IsUnionClosed, pairEmptySingleton]

/-- The universe of $\{\emptyset, \{a\}\}$ is $\{a\}$. -/
theorem pairEmptySingleton_familyUnion (a : α) :
    familyUnion (pairEmptySingleton a) = {a} := by
  simp [familyUnion, pairEmptySingleton]

/-- The number of sets containing $a$ in $\{\emptyset, \{a\}\}$ is 1. -/
theorem pairEmptySingleton_filter_card (a : α) :
    ((pairEmptySingleton a).filter (fun S => a ∈ S)).card = 1 := by
  simp [pairEmptySingleton, Finset.filter_insert, Finset.filter_singleton]

/-- The frequency of $a$ in $\{\emptyset, \{a\}\}$ is exactly $1/2$. -/
theorem pairEmptySingleton_freq (a : α) :
    freq (pairEmptySingleton a) a = 1 / 2 := by
  simp [freq, pairEmptySingleton_filter_card, pairEmptySingleton_card]

/-- Certificate: $\{\emptyset, \{a\}\}$ satisfies Gilmer's constant bound $\ge c_0$. -/
theorem pairEmptySingleton_satisfies_gilmer (a : α) :
    ∃ u ∈ familyUnion (pairEmptySingleton a), c₀ ≤ freq (pairEmptySingleton a) u :=
  ⟨a, (pairEmptySingleton_familyUnion a).symm ▸ Finset.mem_singleton_self a,
    (pairEmptySingleton_freq a).symm ▸ gilmerConstant_lt_half.le⟩

/-- The singleton family $\{\{a\}\}$ is union-closed. -/
theorem singletonFamily_isUnionClosed (a : α) :
    IsUnionClosed (singletonFamily a) := by
  simp [IsUnionClosed, singletonFamily]

/-- The frequency of $a$ in $\{\{a\}\}$ is 1. -/
theorem singletonFamily_freq (a : α) :
    freq (singletonFamily a) a = 1 := by
  simp [freq, singletonFamily, Finset.filter_singleton]

/-- A family of sets is a chain if every pair is comparable under inclusion. -/
def IsChainFamily (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A

/-- Every chain family is union-closed. -/
theorem chainFamily_isUnionClosed (F : Finset (Finset α)) (hchain : IsChainFamily F) :
    IsUnionClosed F := fun A hA B hB =>
  (hchain A hA B hB).elim (fun h => (Finset.union_eq_right.mpr h).symm ▸ hB)
    (fun h => (Finset.union_eq_left.mpr h).symm ▸ hA)

/-- Every powerset $\mathcal{P}(S)$ is union-closed. -/
theorem powerset_isUnionClosed (S : Finset α) :
    IsUnionClosed (Finset.powerset S) :=
  fun _ hA _ hB => Finset.mem_powerset.mpr (Finset.union_subset (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB))

/-- The universe of $\mathcal{P}(S)$ is $S$ when $S$ is non-empty. -/
theorem powerset_familyUnion (S : Finset α) :
    familyUnion (Finset.powerset S) = S := by
  ext; simp [familyUnion]; exact ⟨fun ⟨_, hA, hx⟩ => hA hx, fun hx => ⟨{_}, Finset.singleton_subset_iff.mpr hx, Finset.mem_singleton_self _⟩⟩

/-- Bijection: Sets containing $u$ in $\mathcal{P}(S)$ correspond to $\mathcal{P}(S \setminus \{u\})$. -/
theorem powerset_filter_mem_eq_image (S : Finset α) (u : α) (hu : u ∈ S) :
    ((Finset.powerset S).filter (fun A => u ∈ A)) = (Finset.powerset (S.erase u)).image (insert u) := by
  ext A; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  exact ⟨fun ⟨hA, huA⟩ => ⟨A.erase u, Finset.erase_subset_erase u hA, Finset.insert_erase huA⟩,
    by rintro ⟨B, hB, rfl⟩; exact ⟨Finset.insert_subset hu (hB.trans (Finset.erase_subset u S)), Finset.mem_insert_self u B⟩⟩

/-- The number of subsets of $S$ containing an element $u \in S$ is $2^{|S| - 1}$. -/
theorem powerset_filter_mem_card (S : Finset α) (u : α) (hu : u ∈ S) :
    ((Finset.powerset S).filter (fun A => u ∈ A)).card = 2 ^ (S.card - 1) := by
  rw [powerset_filter_mem_eq_image S u hu, Finset.card_image_of_injOn, Finset.card_powerset, Finset.card_erase_of_mem hu]
  intro A hA B hB heq
  rw [← Finset.erase_insert (fun h => Finset.notMem_erase u S (Finset.mem_powerset.mp hA h)), heq,
    Finset.erase_insert (fun h => Finset.notMem_erase u S (Finset.mem_powerset.mp hB h))]

/-- In any powerset family $\mathcal{P}(S)$, the frequency of every $u \in S$ is exactly $1/2$. -/
theorem powerset_freq (S : Finset α) (u : α) (hu : u ∈ S) :
    freq (Finset.powerset S) u = 1 / 2 := by
  have hS := Nat.sub_add_cancel (Finset.card_pos.mpr ⟨u, hu⟩)
  rw [freq, powerset_filter_mem_card S u hu, Finset.card_powerset]
  nth_rw 2 [← hS]
  rw [pow_succ, Nat.cast_mul, ← div_div, div_self (by positivity)]
  rfl

/-- Powerset families satisfy Frankl's 1/2 conjecture. -/
theorem powerset_satisfies_frankl (S : Finset α) (hS : S.Nonempty) :
    ∃ u ∈ familyUnion (Finset.powerset S), (1 : ℝ) / 2 ≤ freq (Finset.powerset S) u :=
  let ⟨u, hu⟩ := hS; ⟨u, (powerset_familyUnion S).symm ▸ hu, (powerset_freq S u hu).symm.le⟩

/-- Powerset families satisfy Gilmer's constant bound $\ge c_0$. -/
theorem powerset_satisfies_gilmer (S : Finset α) (hS : S.Nonempty) :
    ∃ u ∈ familyUnion (Finset.powerset S), c₀ ≤ freq (Finset.powerset S) u :=
  let ⟨u, hu⟩ := hS; ⟨u, (powerset_familyUnion S).symm ▸ hu, (powerset_freq S u hu).symm ▸ gilmerConstant_lt_half.le⟩

end ConcreteFamilies

end GilmerUnionClosed
