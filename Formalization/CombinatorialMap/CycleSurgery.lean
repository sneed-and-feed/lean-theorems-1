import Formalization.CombinatorialMap.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Ring.Parity

set_option linter.unusedSectionVars false

variable {D : Type*} [Fintype D] [DecidableEq D]

lemma sign_eq_neg_one_pow_card_sub_orbitCount (σ : Equiv.Perm D) :
    (Equiv.Perm.sign σ : ℤ) = (-1) ^ (Fintype.card D - σ.orbitCount) := by
  unfold Equiv.Perm.orbitCount
  have h_int : (Equiv.Perm.sign σ : ℤ) = (-1) ^ (σ.support.card + σ.cycleType.card) := by
    rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sum_cycleType, Units.val_pow_eq_pow_val]; rfl
  have h_le : σ.support.card ≤ Fintype.card D := Finset.card_le_univ _
  have h_le2 : σ.cycleType.card ≤ σ.support.card := by
    rw [← Equiv.Perm.sum_cycleType σ]
    have h_two : (σ.cycleType.card : ℕ) = σ.cycleType.card • 1 := by simp
    rw [h_two]
    apply Multiset.card_nsmul_le_sum
    intro x hx
    exact (Equiv.Perm.two_le_of_mem_cycleType hx).trans' (by decide)
  have h_mod : (σ.support.card + σ.cycleType.card) % 2 = (Fintype.card D - (σ.cycleType.card + (Fintype.card D - σ.support.card))) % 2 := by omega
  rw [h_int, neg_one_pow_eq_pow_mod_two, h_mod, ← neg_one_pow_eq_pow_mod_two]

lemma pow_swap_mul_apply_eq_of_not_sameCycle (σ : Equiv.Perm D) {a b x : D}
    (hx_a : ¬σ.SameCycle x a) (hx_b : ¬σ.SameCycle x b) (n : ℕ) :
    ((Equiv.swap a b * σ) ^ n) x = (σ ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.Perm.mul_apply]
    have h1 : σ.SameCycle x (σ ((σ ^ n) x)) := by
      have : σ ((σ ^ n) x) = (σ ^ (n + 1)) x := by rw [pow_succ', Equiv.Perm.mul_apply]
      rw [this]
      exact ⟨n + 1, rfl⟩
    have hne_a : σ ((σ ^ n) x) ≠ a := fun h => hx_a (h ▸ h1)
    have hne_b : σ ((σ ^ n) x) ≠ b := fun h => hx_b (h ▸ h1)
    rw [Equiv.swap_apply_of_ne_of_ne hne_a hne_b]
    rw [← Equiv.Perm.mul_apply, ← pow_succ']

lemma sameCycle_swap_mul_of_not_sameCycle_both (σ : Equiv.Perm D) {a b x y : D}
    (hx_a : ¬σ.SameCycle x a) (hx_b : ¬σ.SameCycle x b) :
    (Equiv.swap a b * σ).SameCycle x y ↔ σ.SameCycle x y := by
  have h_forward (f : Equiv.Perm D) {u v : D} (hu_a : ¬f.SameCycle u a) (hu_b : ¬f.SameCycle u b)
      (h : f.SameCycle u v) : (Equiv.swap a b * f).SameCycle u v := by
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ), by rw [zpow_natCast, pow_swap_mul_apply_eq_of_not_sameCycle f hu_a hu_b n, hn]⟩
  refine ⟨fun h => ?_, h_forward σ hx_a hx_b⟩
  have h_inv : Equiv.swap a b * (Equiv.swap a b * σ) = σ := by rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
  have h_not_a : ¬(Equiv.swap a b * σ).SameCycle x a := fun h_contra => by
    obtain ⟨n, hn⟩ := h_contra.exists_nat_pow_eq
    exact hx_a ⟨n, by rwa [pow_swap_mul_apply_eq_of_not_sameCycle σ hx_a hx_b n] at hn⟩
  have h_not_b : ¬(Equiv.swap a b * σ).SameCycle x b := fun h_contra => by
    obtain ⟨n, hn⟩ := h_contra.exists_nat_pow_eq
    exact hx_b ⟨n, by rwa [pow_swap_mul_apply_eq_of_not_sameCycle σ hx_a hx_b n] at hn⟩
  exact h_inv ▸ h_forward (Equiv.swap a b * σ) h_not_a h_not_b h

/-
/-- When `a` and `b` are in the same cycle, multiplying by `swap a b` splits the cycle into two,
increasing the total orbit count by 1. -/
lemma orbitCount_swap_mul_eq_add_one_of_sameCycle (σ : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (h : σ.SameCycle a b) :
    (Equiv.swap a b * σ).orbitCount = σ.orbitCount + 1 := by
  sorry

/-- When `a` and `b` are in different cycles, multiplying by `swap a b` merges the two cycles into one,
decreasing the total orbit count by 1. -/
lemma orbitCount_swap_mul_eq_sub_one_of_not_sameCycle (σ : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (h : ¬σ.SameCycle a b) :
    (Equiv.swap a b * σ).orbitCount = σ.orbitCount - 1 := by
  sorry
-/
