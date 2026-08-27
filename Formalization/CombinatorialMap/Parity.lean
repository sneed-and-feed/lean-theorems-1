import Formalization.CombinatorialMap.Basic

open Equiv Perm

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

/-- The sign of the edge involution α is (-1)^E. -/
theorem sign_alpha : sign M.α = (-1 : ℤˣ) ^ M.edgeCount := by
  rw [sign_of_cycleType, alpha_cycleType_card_eq_edgeCount]
  have hsum : M.α.cycleType.sum = 2 * M.edgeCount := by
    rw [alpha_cycleType M, alpha_cycleType_card_eq_edgeCount M]
    simp [Multiset.sum_replicate, mul_comm]
  rw [hsum]
  have : 2 * M.edgeCount + M.edgeCount = 3 * M.edgeCount := by ring
  rw [this, pow_mul]
  have h3 : (-1 : ℤˣ) ^ 3 = -1 := rfl
  rw [h3]

/-- Two exponents give equal powers of (-1) in ℤˣ if their sum is even. -/
theorem neg_one_pow_eq_of_even_add {a b : ℕ} (h : Even (a + b)) :
    (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b := by
  obtain ⟨k, hk⟩ := h
  have hpow : (-1 : ℤˣ) ^ (a + b) = 1 := by
    rw [hk, ← two_mul, pow_mul]
    have : (-1 : ℤˣ) ^ 2 = 1 := rfl
    rw [this, one_pow]
  rw [pow_add] at hpow
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ b) with hb | hb
  · rw [hb, mul_one] at hpow
    rw [hpow, hb]
  · rw [hb] at hpow ⊢
    rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ a) with ha | ha
    · rw [ha] at hpow
      have : (1 : ℤˣ) * -1 = -1 := rfl
      rw [this] at hpow
      cases hpow
    · exact ha

/-- The sign of the vertex permutation σ is (-1)^V. -/
theorem sign_sigma : sign M.σ = (-1 : ℤˣ) ^ M.vertexCount := by
  rw [sign_of_cycleType]
  apply neg_one_pow_eq_of_even_add
  have hfp := Equiv.Perm.card_fixedPoints M.σ
  have hsum_le := Equiv.Perm.sum_cycleType_le M.σ
  have hD := card_darts_eq_two_mul_edgeCount M
  unfold vertexCount
  use (M.edgeCount + M.σ.cycleType.card)
  omega

/-- The sign of the face permutation φ = σ * α is (-1)^F. -/
theorem sign_phi : sign M.φ = (-1 : ℤˣ) ^ M.faceCount := by
  rw [sign_of_cycleType]
  apply neg_one_pow_eq_of_even_add
  have hfp := Equiv.Perm.card_fixedPoints M.φ
  have hsum_le := Equiv.Perm.sum_cycleType_le M.φ
  have hD := card_darts_eq_two_mul_edgeCount M
  unfold faceCount
  use (M.edgeCount + M.φ.cycleType.card)
  omega

/-- Parity identity: (-1)^(V + E + F) = 1 for every combinatorial map. -/
theorem eulerChar_parity : (-1 : ℤˣ) ^ (M.vertexCount + M.edgeCount + M.faceCount) = 1 := by
  have hsign : sign M.φ = sign M.σ * sign M.α := by
    unfold φ
    exact sign_mul M.σ M.α
  rw [sign_phi, sign_sigma, sign_alpha, ← pow_add] at hsign
  have h_sq : (-1 : ℤˣ) ^ (M.vertexCount + M.edgeCount + M.faceCount) =
      ((-1 : ℤˣ) ^ (M.vertexCount + M.edgeCount)) * ((-1 : ℤˣ) ^ M.faceCount) := by rw [pow_add]
  rw [h_sq, ← hsign]
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ M.faceCount) with hf | hf
  · rw [hf]; rfl
  · rw [hf]; rfl

/-- The sum V + E + F is always even for any combinatorial map. -/
theorem eulerChar_is_even : Even (M.vertexCount + M.edgeCount + M.faceCount) := by
  have hpar := eulerChar_parity M
  by_contra h_odd
  have h_odd' : Odd (M.vertexCount + M.edgeCount + M.faceCount) := Nat.not_even_iff_odd.mp h_odd
  obtain ⟨k, hk⟩ := h_odd'
  rw [hk, pow_add, pow_mul] at hpar
  have h2 : (-1 : ℤˣ) ^ 2 = 1 := rfl
  rw [h2, one_pow, one_mul] at hpar
  have h1 : (-1 : ℤˣ) ^ 1 = -1 := rfl
  rw [h1] at hpar
  cases hpar

/-- The Euler characteristic χ(M) = V - E + F is always an even integer. -/
theorem eulerChar_int_is_even : ∃ k : ℤ, M.eulerChar = 2 * k := by
  have heven := eulerChar_is_even M
  obtain ⟨k, hk⟩ := heven
  unfold eulerChar
  use (k - M.edgeCount)
  omega

end CombinatorialMap