import Mathlib.Algebra.Module.Defs
import Mathlib.Tactic.Abel

open Module

/-- Desargues's Theorem (Vector Formulation):
    Two triangles in central perspective from O have their side-intersection points
    P, Q, R satisfying a linear dependence relation ν • P + λ • Q + μ • R = 0 (axial perspective / collinearity). -/
theorem desargues_vector {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (O A₁ B₁ C₁ A₂ B₂ C₂ : V)
    (a b c «λ» μ ν : K)
    (hA₂ : A₂ = a • A₁ + «λ» • O)
    (hB₂ : B₂ = b • B₁ + μ • O)
    (hC₂ : C₂ = c • C₁ + ν • O)
    (P Q R : V)
    (hP : P = μ • A₂ - «λ» • B₂)
    (hQ : Q = ν • B₂ - μ • C₂)
    (hR : R = «λ» • C₂ - ν • A₂) :
    ν • P + «λ» • Q + μ • R = 0 ∧
    P = (μ * a) • A₁ - («λ» * b) • B₁ ∧
    Q = (ν * b) • B₁ - (μ * c) • C₁ ∧
    R = («λ» * c) • C₁ - (ν * a) • A₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hP, hQ, hR]
      simp only [smul_sub, ← mul_smul]
      rw [mul_comm ν μ, mul_comm «λ» ν, mul_comm μ «λ»]
      abel
    · rw [hP, hA₂, hB₂]
      simp only [smul_add, ← mul_smul]
      rw [mul_comm μ «λ»]
      abel
    · rw [hQ, hB₂, hC₂]
      simp only [smul_add, ← mul_smul]
      rw [mul_comm ν μ]
      abel
    · rw [hR, hC₂, hA₂]
      simp only [smul_add, ← mul_smul]
      rw [mul_comm «λ» ν]
      abel


