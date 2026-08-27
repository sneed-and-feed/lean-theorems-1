import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Sign

/-!
# Combinatorial Maps (Rotation Systems)

This module formalizes the Tutte–Edmonds framework for combinatorial maps (rotation systems /
hyperimaps) on finite dart sets.

A combinatorial map is a finite set of darts D equipped with:
- an edge involution α : Perm D with no fixed points (α * α = 1 and ∀ d, α d ≠ d), and
- a vertex permutation σ : Perm D giving the cyclic order of darts around each vertex.

Faces are traced by the permutation φ := σ * α.
-/

open Equiv Perm

/-- A combinatorial map on a finite set of darts D. -/
structure CombinatorialMap (D : Type*) [Fintype D] [DecidableEq D] where
  α : Perm D
  σ : Perm D
  α_involution : α * α = 1
  α_no_fixed_points : ∀ d, α d ≠ d

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

/-- The face permutation φ = σ * α tracing darts around face boundaries. -/
def φ : Perm D := M.σ * M.α

/-- The number of vertices, counted as the number of orbits (cycles + fixed points) of σ. -/
def vertexCount : ℕ := M.σ.cycleType.card + Fintype.card (Function.fixedPoints M.σ)

/-- The number of edges, equal to half the number of darts (|D| / 2). -/
def edgeCount (_ : CombinatorialMap D) : ℕ := Fintype.card D / 2

/-- The number of faces, counted as the number of orbits of φ = σ * α. -/
def faceCount : ℕ := M.φ.cycleType.card + Fintype.card (Function.fixedPoints M.φ)

/-- The Euler characteristic of a combinatorial map: χ(M) = V - E + F. -/
def eulerChar : ℤ := (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ)

/-- Fixed points of α are empty since α is fixed-point free. -/
theorem fixedPoints_alpha_isEmpty : IsEmpty (Function.fixedPoints M.α) :=
  ⟨fun ⟨x, hx⟩ => M.α_no_fixed_points x hx⟩

/-- The number of fixed points of α is 0. -/
theorem fixedPoints_alpha_card : Fintype.card (Function.fixedPoints M.α) = 0 := by
  have : IsEmpty (Function.fixedPoints M.α) := fixedPoints_alpha_isEmpty M
  exact Fintype.card_eq_zero

/-- The cycle type of the edge involution α consists solely of 2-cycles. -/
theorem alpha_cycleType : M.α.cycleType = Multiset.replicate M.α.cycleType.card 2 := by
  have h2 : M.α ^ 2 = 1 := by rw [sq, M.α_involution]
  exact cycleType_of_pow_prime_eq_one h2

/-- The number of darts is exactly twice the number of 2-cycles of α. -/
theorem card_darts_eq_two_mul_alpha_cycleType_card :
    Fintype.card D = 2 * M.α.cycleType.card := by
  have hfp := fixedPoints_alpha_card M
  have hcard := Equiv.Perm.card_fixedPoints M.α
  have hsum : M.α.cycleType.sum = 2 * M.α.cycleType.card := by
    rw [alpha_cycleType M]
    simp [Multiset.sum_replicate, mul_comm]
  have hsum_le := Equiv.Perm.sum_cycleType_le M.α
  omega

/-- The number of darts is exactly twice the edge count. -/
theorem card_darts_eq_two_mul_edgeCount :
    Fintype.card D = 2 * M.edgeCount := by
  unfold edgeCount
  have := card_darts_eq_two_mul_alpha_cycleType_card M
  omega

/-- The number of 2-cycles of α equals the edge count. -/
theorem alpha_cycleType_card_eq_edgeCount :
    M.α.cycleType.card = M.edgeCount := by
  have h1 := card_darts_eq_two_mul_alpha_cycleType_card M
  have h2 := card_darts_eq_two_mul_edgeCount M
  omega

end CombinatorialMap