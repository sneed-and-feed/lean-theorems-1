import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GilmerUnionClosed

/-!
# Union-Closed Families and Frequency Marginal Properties

This module defines fundamental concepts for Frankl's Union-Closed Sets Conjecture:
- `IsUnionClosed`: A family of sets closed under pairwise unions.
- `IsIntersectionClosed`: A family of sets closed under pairwise intersections.
- `familyUnion`: The universe/support of a family (union of all member sets).
- `freq`: The frequency/marginal probability $p_u = |\{S \in F \mid u \in S\}| / |F|$.
- Core analytical properties: non-negativity, boundedness, zero-frequency characterization,
  positivity on universe support, and unit frequency.
-/

section Definitions

/-- A family of sets `F` is union-closed if the union of any two members of `F` is also in `F`. -/
def IsUnionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ∪ B ∈ F

/-- A family of sets `F` is intersection-closed if the intersection of any two members is in `F`. -/
def IsIntersectionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ∩ B ∈ F

/-- The total universe (support) of a family of sets `F`, defined as the union of all sets in `F`. -/
def familyUnion {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

/-- The frequency / marginal probability of an element `u` in a family `F`,
defined as the fraction of sets in `F` that contain `u`. -/
noncomputable def freq {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (u : α) : ℝ :=
  (F.filter (fun S => u ∈ S)).card / (F.card : ℝ)

end Definitions

section FrequencyProperties

variable {α : Type*} [DecidableEq α]

/-- The frequency of any element is non-negative. -/
theorem freq_nonneg (F : Finset (Finset α)) (u : α) : 0 ≤ freq F u :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The frequency of any element is at most 1. -/
theorem freq_le_one (F : Finset (Finset α)) (u : α) : freq F u ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (Nat.cast_nonneg _)

/-- If `u` is not in the universe of `F`, its frequency is 0. -/
theorem freq_eq_zero_of_not_mem_familyUnion (F : Finset (Finset α)) (u : α)
    (hu : u ∉ familyUnion F) : freq F u = 0 := by
  have : F.filter (fun S => u ∈ S) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun S hS huS => hu (Finset.mem_biUnion.mpr ⟨S, hS, huS⟩)
  simp [freq, this]

/-- If `u` is in the universe of `F`, its frequency is strictly positive. -/
theorem freq_pos_of_mem_familyUnion (F : Finset (Finset α)) (u : α)
    (hu : u ∈ familyUnion F) : 0 < freq F u := by
  rcases Finset.mem_biUnion.mp hu with ⟨S, hS, huS⟩
  exact div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, huS⟩⟩))
    (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨S, hS⟩))

/-- If an element `u` belongs to every set in `F`, its frequency is 1 (provided `F` is nonempty). -/
theorem freq_eq_one_of_forall_mem (F : Finset (Finset α)) (hF : F.Nonempty) (u : α)
    (hu : ∀ S ∈ F, u ∈ S) : freq F u = 1 := by
  simp [freq, Finset.filter_eq_self.mpr hu, hF.ne_empty]

end FrequencyProperties

end GilmerUnionClosed
