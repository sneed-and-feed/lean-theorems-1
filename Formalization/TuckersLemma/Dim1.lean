import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# 1D Tucker's Lemma & Discrete Sign-Change Parity

This module formalizes:
1. **Discrete Intermediate Value Theorem / Sign Change:**
   For any discrete path of length `N` labeled in `{±1}`, if the endpoints have opposite
   signs, there exists at least one adjacent pair with opposite signs.
2. **1D Tucker's Lemma:**
   An antipodal labeling of a 1D symmetric subdivision $[-1, 1]$ with $2n+1$ vertices
   has an adjacent complementary edge.
3. **1D Parity Conservation:**
   The exact count of sign-switching edges along any sequence in `{±1}` has the same parity
   modulo 2 as the endpoint difference.
-/

namespace TuckersLemma

section Dim1

/-- Discrete sign change theorem on a 1D chain of length `N`:
    If a sequence of signs `s : Fin (N + 1) → {±1}` starts and ends with opposite signs,
    there must exist an adjacent transition with `s(i) = -s(i+1)`. -/
lemma exists_adjacent_sign_change : ∀ (N : ℕ) (s : Fin (N + 1) → ℤ),
    (∀ i, s i = 1 ∨ s i = -1) →
    s 0 ≠ s ⟨N, by omega⟩ →
    ∃ (i : ℕ) (hi : i < N), s ⟨i, by omega⟩ = - s ⟨i + 1, by omega⟩
  | 0, _, _, h_diff => (h_diff rfl).elim
  | n + 1, s, h_val, h_diff => by
    by_cases h_step : s ⟨n, by omega⟩ = s ⟨n + 1, by omega⟩
    · obtain ⟨i, hi, h_opp⟩ := exists_adjacent_sign_change n (fun j => s ⟨j.val, by omega⟩) (fun j => h_val _) (by intro h; apply h_diff; exact h.trans h_step)
      exact ⟨i, by omega, h_opp⟩
    · refine ⟨n, by omega, ?_⟩
      obtain h1 | h1 := h_val ⟨n, by omega⟩ <;> obtain h2 | h2 := h_val ⟨n + 1, by omega⟩ <;> omega

/-- **1D Tucker's Lemma (Tucker 1945):**
    For any antipodal sequence on `2n+1` vertices with `L(0) = -L(2n) ∈ {±1}`,
    there exists an adjacent complementary edge. -/
theorem tucker_1d (n : ℕ)
    (L : Fin (2 * n + 1) → ℤ)
    (h_range : ∀ i, L i = 1 ∨ L i = -1)
    (h_antipodal : L 0 = - L ⟨2 * n, by omega⟩) :
    ∃ (i : ℕ) (hi : i < 2 * n), L ⟨i, by omega⟩ = - L ⟨i + 1, by omega⟩ := by
  apply exists_adjacent_sign_change (2 * n) L h_range
  intro h
  obtain h1 | h1 := h_range 0 <;> omega

/-- Three-element sign transition parity: addition mod 2 of transitions is transitive on `{±1}`. -/
lemma sign_trans_parity (a b c : ℤ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) (hc : c = 1 ∨ c = -1) :
    ((if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0)) % 2 =
    if a ≠ c then 1 else 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl

/-- Total number of sign switches along a 1D path of length `n`. -/
def switchCount1D (n : ℕ) (s : Fin (n + 1) → ℤ) : ℕ :=
  ∑ i : Fin n, if s i.castSucc ≠ s i.succ then 1 else 0

lemma switchCount1D_succ (n : ℕ) (s : Fin (n + 2) → ℤ) :
    switchCount1D (n + 1) s =
    (if s 0 ≠ s 1 then 1 else 0) + switchCount1D n (fun i => s i.succ) := by
  dsimp [switchCount1D]
  rw [Fin.sum_univ_succ]
  rfl

/-- **1D Sign Switch Parity Theorem:**
    The number of sign switches along a path is odd if and only if the endpoints have opposite signs. -/
theorem sign_switch_parity (n : ℕ) (s : Fin (n + 1) → ℤ)
    (h_range : ∀ i, s i = 1 ∨ s i = -1) :
    (switchCount1D n s) % 2 = if s 0 ≠ s ⟨n, by omega⟩ then 1 else 0 := by
  induction n with
  | zero => simp [switchCount1D]
  | succ n ih =>
    rw [switchCount1D_succ n s, Nat.add_mod]
    have ih_g := ih (fun i => s i.succ) (fun i => h_range i.succ)
    have h_trans := sign_trans_parity (s 0) (s 1) (s ⟨n + 1, by omega⟩)
      (h_range 0) (h_range 1) (h_range ⟨n + 1, by omega⟩)
    have h_one : (Fin.succ (0 : Fin (n + 1))) = 1 := rfl
    have h_last : (Fin.succ (⟨n, by omega⟩ : Fin (n + 1))) = ⟨n + 1, by omega⟩ := rfl
    rw [h_one, h_last] at ih_g
    rw [ih_g]
    omega

/-- Existence of adjacent sign switch from odd switch count parity. -/
theorem tucker_1d_parity_exists (n : ℕ) (s : Fin (n + 1) → ℤ)
    (h_range : ∀ i, s i = 1 ∨ s i = -1)
    (h_diff : s 0 ≠ s ⟨n, by omega⟩) :
    ∃ i : Fin n, s i.castSucc = - s i.succ := by
  have h_odd : (switchCount1D n s) % 2 = 1 := by
    rw [sign_switch_parity n s h_range]
    simp [h_diff]
  have h_pos : 0 < switchCount1D n s := by omega
  by_contra! h_none
  have h_zero : switchCount1D n s = 0 := by
    dsimp [switchCount1D]
    apply Finset.sum_eq_zero
    intro i _
    have hi1 := h_range i.castSucc
    have hi2 := h_range i.succ
    have h_opp : s i.castSucc ≠ - s i.succ := h_none i
    have h_eq : s i.castSucc = s i.succ := by
      rcases hi1 with h1 | h1 <;> rcases hi2 with h2 | h2 <;> omega
    simp [h_eq]
  rw [h_zero] at h_pos
  omega

end Dim1

end TuckersLemma
