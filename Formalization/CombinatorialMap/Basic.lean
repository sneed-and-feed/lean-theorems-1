import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Defs

variable {D : Type*} [Fintype D] [DecidableEq D]

structure CombinatorialMap (D : Type*) [Fintype D] [DecidableEq D] where
  α : Equiv.Perm D
  σ : Equiv.Perm D
  α_inv : α * α = 1
  α_fpf : ∀ d, α d ≠ d

noncomputable def Equiv.Perm.orbitCount (σ : Equiv.Perm D) : ℕ :=
  Multiset.card σ.cycleType + (Fintype.card D - Finset.card σ.support)

namespace CombinatorialMap

variable (M : CombinatorialMap D)

def facePerm : Equiv.Perm D := M.σ * M.α

noncomputable def vertexCount : ℕ := M.σ.orbitCount

noncomputable def edgeCount (_M : CombinatorialMap D) : ℕ := Fintype.card D / 2

noncomputable def faceCount : ℕ := M.facePerm.orbitCount

noncomputable def eulerChar : ℤ := (vertexCount M : ℤ) - (edgeCount M : ℤ) + (faceCount M : ℤ)

/-- A combinatorial map is planar (spherical / genus 0) if its Euler characteristic is 2. -/
def IsPlanar : Prop :=
  M.eulerChar = 2

lemma α_sq : M.α ^ 2 = 1 := by
  rw [sq, M.α_inv]

lemma α_self_inverse : M.α⁻¹ = M.α := by
  calc M.α⁻¹ = M.α⁻¹ * 1 := by rw [mul_one]
    _ = M.α⁻¹ * (M.α * M.α) := by rw [M.α_inv]
    _ = (M.α⁻¹ * M.α) * M.α := by rw [← mul_assoc]
    _ = 1 * M.α := by rw [inv_mul_cancel]
    _ = M.α := by rw [one_mul]

lemma edgeCount_eq : M.edgeCount = Fintype.card D / 2 := rfl

lemma dart_count_even (M : CombinatorialMap D) : 2 ∣ Fintype.card D := by
  have h1 : M.α ^ 2 = 1 := α_sq M
  have h2 : M.α.cycleType = Multiset.replicate M.α.cycleType.card 2 := Equiv.Perm.cycleType_of_pow_prime_eq_one h1
  have h3 : M.α.support = Finset.univ := by
    ext d
    simp [Equiv.Perm.mem_support, M.α_fpf]
  have h4 : M.α.cycleType.sum = M.α.support.card := Equiv.Perm.sum_cycleType M.α
  rw [h2, Multiset.sum_replicate, nsmul_eq_mul, mul_comm] at h4
  rw [h3, Finset.card_univ] at h4
  exact ⟨M.α.cycleType.card, h4.symm⟩

lemma orbitCount_one : Equiv.Perm.orbitCount (1 : Equiv.Perm D) = Fintype.card D := by
  simp [Equiv.Perm.orbitCount]

end CombinatorialMap