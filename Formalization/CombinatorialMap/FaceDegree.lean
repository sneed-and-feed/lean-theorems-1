import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Formalization.CombinatorialMap.Basic

/-!
# Face Degrees and Handshaking Invariants for Combinatorial Maps

This module establishes the face-cycle sum inequalities for combinatorial maps:
1. `three_mul_card_le_sum`: If every cycle in σ.cycleType has length ≥ 3, then 3 * |cycleType| ≤ sum(cycleType).
2. `four_mul_card_le_sum`: If every cycle in σ.cycleType has length ≥ 4, then 4 * |cycleType| ≤ sum(cycleType).
3. `three_mul_faceCount_le_two_mul_edgeCount`: Deduces 3F ≤ 2E for maps without monogons and face cycle lengths ≥ 3.
4. `four_mul_faceCount_le_two_mul_edgeCount`: Deduces 4F ≤ 2E for triangle-free maps without monogons and face cycle lengths ≥ 4.
-/

open Equiv Perm

namespace CombinatorialMap

/-- Cycle sum inequality: if every cycle has length at least `k`,
then `k * σ.cycleType.card ≤ σ.cycleType.sum`. -/
lemma k_mul_card_le_sum (k : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α)
    (h_gek : ∀ n ∈ σ.cycleType, k ≤ n) : k * σ.cycleType.card ≤ σ.cycleType.sum := by
  simpa [nsmul_eq_mul, mul_comm] using Multiset.card_nsmul_le_sum h_gek

/-- Cycle sum inequality for cycle length ≥ 3: 3 * |cycleType| ≤ sum(cycleType). -/
lemma three_mul_card_le_sum {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α)
    (h_gt2 : ∀ n ∈ σ.cycleType, 3 ≤ n) : 3 * σ.cycleType.card ≤ σ.cycleType.sum :=
  k_mul_card_le_sum 3 σ h_gt2

/-- Cycle sum inequality for cycle length ≥ 4: 4 * |cycleType| ≤ sum(cycleType). -/
lemma four_mul_card_le_sum {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α)
    (h_gt3 : ∀ n ∈ σ.cycleType, 4 ≤ n) : 4 * σ.cycleType.card ≤ σ.cycleType.sum :=
  k_mul_card_le_sum 4 σ h_gt3

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

/-- General handshaking inequality: for any map whose face cycles have length at least `k`
and no monogons, `k * M.faceCount ≤ 2 * M.edgeCount`. -/
theorem k_mul_faceCount_le_two_mul_edgeCount (k : ℕ)
    (h_mono : Function.fixedPoints M.φ = ∅)
    (h_gek : ∀ n ∈ M.φ.cycleType, k ≤ n) :
    k * M.faceCount ≤ 2 * M.edgeCount := by
  rw [M.faceCount_eq_cycleType_card h_mono]
  have h1 := k_mul_card_le_sum k M.φ h_gek
  have h2 := Equiv.Perm.sum_cycleType_le M.φ
  have := card_darts_eq_two_mul_edgeCount M
  exact (h1.trans h2).trans (by omega)

/-- For any map whose face cycles have length ≥ 3 and no fixed points (monogons),
3 * M.faceCount ≤ 2 * M.edgeCount. -/
theorem three_mul_faceCount_le_two_mul_edgeCount
    (h_mono : Function.fixedPoints M.φ = ∅)
    (h_gt2 : ∀ n ∈ M.φ.cycleType, 3 ≤ n) :
    3 * M.faceCount ≤ 2 * M.edgeCount :=
  k_mul_faceCount_le_two_mul_edgeCount M 3 h_mono h_gt2

/-- For any triangle-free map whose face cycles have length ≥ 4 and no fixed points (monogons),
4 * M.faceCount ≤ 2 * M.edgeCount. -/
theorem four_mul_faceCount_le_two_mul_edgeCount
    (h_mono : Function.fixedPoints M.φ = ∅)
    (h_gt3 : ∀ n ∈ M.φ.cycleType, 4 ≤ n) :
    4 * M.faceCount ≤ 2 * M.edgeCount :=
  k_mul_faceCount_le_two_mul_edgeCount M 4 h_mono h_gt3

end CombinatorialMap
