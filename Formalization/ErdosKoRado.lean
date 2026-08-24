import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.KatonaCircle
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Finset

/-!
# Erdős–Ko–Rado Theorem via Katona's Circle Method

This module formalizes the **Erdős–Ko–Rado (EKR) Theorem** (P. Erdős, C. Ko, R. Rado, 1961)
on intersecting families of finite sets using **Katona's Circle Method** (G. O. H. Katona, 1972).

## Main Results
- `katona_arc_lemma`: If `I ⊆ ZMod n` indexes pairwise intersecting cyclic arcs of length `k`,
  and `2k ≤ n`, then `|I| ≤ k`.
- `choose_bound_of_double_counting`: Exact factorial cancellation yielding `|ℱ| ≤ Nat.choose (n - 1) (k - 1)`.
- `erdos_ko_rado`: If `ℱ` is an intersecting family of `k`-element subsets of an `n`-element set
  with `n ≥ 2k` and `k ≥ 1`, then `|ℱ| ≤ Nat.choose (n - 1) (k - 1)`.
- `erdos_ko_rado_disjoint_pair`: If `|ℱ| > Nat.choose (n - 1) (k - 1)`, then `ℱ` contains two disjoint sets.
- `erdos_ko_rado_powersetCard`: Intersecting subfamily of `(Finset.univ : Finset α).powersetCard k`.
- `exists_hiltonMilner_extremizer`: The Hilton--Milner bound is attained by the classical
  exceptional-set construction, which is proved uniform, intersecting, and non-star.

## References

- P. Erdős, C. Ko, and R. Rado, *Intersection theorems for systems of finite sets*,
  Q. J. Math. **12** (1961), 313--320, doi:10.1093/qmath/12.1.313.
- A. J. W. Hilton and E. C. Milner, *Some intersection theorems for systems of finite sets*,
  Q. J. Math. **18** (1967), 369--384, doi:10.1093/qmath/18.1.369.
- D. Bulavka and R. Woodroofe, *A short proof of the Hilton--Milner Theorem*,
  Canad. Math. Bull. **69** (2026), 603--608, Theorem 1,
  doi:10.4153/S000843952510132X (CC BY-SA 4.0).
-/

/-- The cyclic arc of length `k` starting at position `i` in `ZMod n`. -/
def cyclicArc (n k : ℕ) (i : ZMod n) : Finset (ZMod n) :=
  Finset.image (fun (j : ℕ) => i + (j : ZMod n)) (Finset.range k)

lemma mem_cyclicArc_iff {n k : ℕ} {i x : ZMod n} :
    x ∈ cyclicArc n k i ↔ ∃ j < k, x = i + (j : ZMod n) := by
  simp only [cyclicArc, mem_image, mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

lemma mem_cyclicArc_zero_iff {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) (x : ZMod n) :
    x ∈ cyclicArc n k 0 ↔ x.val < k := by
  have : NeZero n := ⟨by omega⟩
  rw [mem_cyclicArc_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [zero_add]
    rw [ZMod.val_natCast_of_lt (by omega)]
    exact hj
  · intro hx
    refine ⟨x.val, hx, ?_⟩
    simp only [zero_add]
    exact (ZMod.natCast_zmod_val x).symm

lemma cyclicArc_card {n k : ℕ} (i : ZMod n) (hkn : k ≤ n) (hn : 0 < n) :
    (cyclicArc n k i).card = k := by
  have : NeZero n := ⟨by omega⟩
  rw [cyclicArc]
  rw [card_image_of_injOn]
  · rw [card_range]
  · intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_range] at hx hy
    dsimp at hxy
    simp only [add_right_inj] at hxy
    have hx_val : ((x : ZMod n).val) = x := ZMod.val_natCast_of_lt (by omega)
    have hy_val : ((y : ZMod n).val) = y := ZMod.val_natCast_of_lt (by omega)
    have h_val := congr_arg ZMod.val hxy
    rw [hx_val, hy_val] at h_val
    exact h_val

lemma cyclicArc_disjoint {n k : ℕ} (h2k : 2 * k ≤ n) (hk : 1 ≤ k) (r : ℕ) (_hr1 : 1 ≤ r) (_hr2 : r ≤ k - 1) :
    Disjoint (cyclicArc n k (r : ZMod n)) (cyclicArc n k ((r : ZMod n) - (k : ZMod n))) := by
  have : NeZero n := ⟨by omega⟩
  rw [disjoint_iff_ne]
  intro x hx y hy hxy
  rw [mem_cyclicArc_iff] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have h_zero_mod : (r : ZMod n) + (a : ZMod n) - ((r : ZMod n) - (k : ZMod n) + (b : ZMod n)) = 0 := by
    rw [hxy, sub_self]
  have h_cast : ((k + a - b : ℕ) : ZMod n) = (k : ZMod n) + (a : ZMod n) - (b : ZMod n) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
  have h_sub : (r : ZMod n) + (a : ZMod n) - ((r : ZMod n) - (k : ZMod n) + (b : ZMod n)) =
      ((k + a - b : ℕ) : ZMod n) := by
    rw [h_cast]
    ring
  rw [h_sub] at h_zero_mod
  have h_bounds : 1 ≤ k + a - b ∧ k + a - b < n := by
    omega
  have h_mod : ((k + a - b : ℕ) : ZMod n).val = k + a - b :=
    ZMod.val_natCast_of_lt h_bounds.2
  have h_zero : ((k + a - b : ℕ) : ZMod n).val = 0 := by
    rw [h_zero_mod, ZMod.val_zero]
  rw [h_zero] at h_mod
  omega

lemma mem_pair_of_intersect_zero {n k : ℕ} (h2k : 2 * k ≤ n) (hk : 1 ≤ k) (i : ZMod n)
    (h_inter : ¬ Disjoint (cyclicArc n k i) (cyclicArc n k 0)) (hi_ne : i ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ k - 1 ∧ (i = (r : ZMod n) ∨ i = (r : ZMod n) - (k : ZMod n)) := by
  have : NeZero n := ⟨by omega⟩
  rw [Finset.disjoint_iff_ne] at h_inter
  push Not at h_inter
  obtain ⟨x, hx, y, hy, rfl⟩ := h_inter
  rw [mem_cyclicArc_iff] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hy_eq⟩ := hy
  simp only [zero_add] at hy_eq
  have h_eq : i = (b : ZMod n) - (a : ZMod n) := by
    linear_combination hy_eq
  by_cases hba : a < b
  · refine ⟨b - a, by omega, by omega, Or.inl ?_⟩
    rw [h_eq]
    have : ((b - a : ℕ) : ZMod n) = (b : ZMod n) - (a : ZMod n) := Nat.cast_sub (by omega)
    rw [this]
  · have hba_le : b ≤ a := not_lt.mp hba
    have hba_ne : b ≠ a := by
      rintro rfl
      rw [sub_self] at h_eq
      exact hi_ne h_eq
    have hba_lt : b < a := lt_of_le_of_ne hba_le hba_ne
    refine ⟨k - (a - b), by omega, by omega, Or.inr ?_⟩
    rw [h_eq]
    have h1 : ((k - (a - b) : ℕ) : ZMod n) = (k : ZMod n) - ((a - b : ℕ) : ZMod n) := Nat.cast_sub (by omega)
    have h2 : ((a - b : ℕ) : ZMod n) = (a : ZMod n) - (b : ZMod n) := Nat.cast_sub (by omega)
    rw [h1, h2]
    ring

lemma cyclicArc_sub {n k : ℕ} (i c : ZMod n) :
    cyclicArc n k (i - c) = (cyclicArc n k i).image (fun x => x - c) := by
  ext x
  rw [mem_cyclicArc_iff, mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨i + (j : ZMod n), ?_, ?_⟩
    · rw [mem_cyclicArc_iff]
      exact ⟨j, hj, rfl⟩
    · ring
  · rintro ⟨y, hy, rfl⟩
    rw [mem_cyclicArc_iff] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    refine ⟨j, hj, ?_⟩
    ring

lemma katona_arc_lemma_zero {n k : ℕ} (h2k : 2 * k ≤ n) (hk : 1 ≤ k)
    (I : Finset (ZMod n)) (h0 : 0 ∈ I)
    (h_inter : ∀ i ∈ I, ∀ j ∈ I, ¬ Disjoint (cyclicArc n k i) (cyclicArc n k j)) :
    I.card ≤ k := by
  have : NeZero n := ⟨by omega⟩
  let I0 := I.erase 0
  have hI_split : I.card = I0.card + 1 := by
    have : 0 < I.card := Finset.card_pos.mpr ⟨0, h0⟩
    rw [Finset.card_erase_of_mem h0]
    omega
  let pair (r : ℕ) : Finset (ZMod n) := {(r : ZMod n), (r : ZMod n) - (k : ZMod n)}
  have h_pair_le (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ k - 1) : (I ∩ pair r).card ≤ 1 := by
    by_contra! h_gt
    have h_pair_two : (pair r).card ≤ 2 := card_insert_le _ _
    have h_eq_pair : I ∩ pair r = pair r := by
      apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_right)
      omega
    have h_r_in : (r : ZMod n) ∈ I := by
      have : (r : ZMod n) ∈ pair r := by simp [pair]
      rw [← h_eq_pair] at this
      exact (Finset.mem_inter.mp this).1
    have h_rk_in : (r : ZMod n) - (k : ZMod n) ∈ I := by
      have : (r : ZMod n) - (k : ZMod n) ∈ pair r := by simp [pair]
      rw [← h_eq_pair] at this
      exact (Finset.mem_inter.mp this).1
    have h_disj := cyclicArc_disjoint h2k hk r hr1 hr2
    have h_not_disj := h_inter (r : ZMod n) h_r_in ((r : ZMod n) - (k : ZMod n)) h_rk_in
    exact h_not_disj h_disj
  have h_I0_sub : I0 ⊆ (Finset.Ico 1 k).biUnion (fun r => I ∩ pair r) := by
    intro i hi
    rw [mem_erase] at hi
    have h_inter_zero := h_inter i hi.2 0 h0
    obtain ⟨r, hr1, hr2, hr_cases⟩ := mem_pair_of_intersect_zero h2k hk i h_inter_zero hi.1
    rw [mem_biUnion]
    refine ⟨r, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · rw [mem_inter]
      refine ⟨hi.2, ?_⟩
      dsimp [pair]
      rcases hr_cases with rfl | rfl
      · simp
      · simp
  have h_I0_card : I0.card ≤ ∑ r ∈ Finset.Ico 1 k, (I ∩ pair r).card := by
    apply le_trans (Finset.card_le_card h_I0_sub)
    exact Finset.card_biUnion_le
  have h_sum_le : (∑ r ∈ Finset.Ico 1 k, (I ∩ pair r).card) ≤ ∑ r ∈ Finset.Ico 1 k, 1 := by
    apply Finset.sum_le_sum
    intro r hr
    rw [Finset.mem_Ico] at hr
    exact h_pair_le r hr.1 (by omega)
  rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico] at h_sum_le
  have h_I0_bound : I0.card ≤ k - 1 := h_I0_card.trans h_sum_le
  omega

theorem katona_arc_lemma {n k : ℕ} (h2k : 2 * k ≤ n) (hk : 1 ≤ k)
    (I : Finset (ZMod n))
    (h_inter : ∀ i ∈ I, ∀ j ∈ I, ¬ Disjoint (cyclicArc n k i) (cyclicArc n k j)) :
    I.card ≤ k := by
  by_cases hI_emp : I = ∅
  · rw [hI_emp, Finset.card_empty]
    omega
  · obtain ⟨i0, hi0⟩ := Finset.nonempty_of_ne_empty hI_emp
    let f : ZMod n → ZMod n := fun x => x - i0
    let I' := I.image f
    have hf_inj : Function.Injective f := fun x y h => by
      dsimp [f] at h
      linear_combination h
    have hI'_card : I'.card = I.card := Finset.card_image_of_injective I hf_inj
    have h0_in : 0 ∈ I' := by
      rw [mem_image]
      refine ⟨i0, hi0, ?_⟩
      dsimp [f]
      ring
    have h_inter' : ∀ i ∈ I', ∀ j ∈ I', ¬ Disjoint (cyclicArc n k i) (cyclicArc n k j) := by
      intro i hi j hj
      rw [mem_image] at hi hj
      obtain ⟨x, hx, rfl⟩ := hi
      obtain ⟨y, hy, rfl⟩ := hj
      have hxy_inter := h_inter x hx y hy
      dsimp [f]
      rw [cyclicArc_sub x i0, cyclicArc_sub y i0]
      intro h_disj
      have hf_emb : Function.Injective (fun a : ZMod n => a - i0) := fun a b h => by
        dsimp at h; linear_combination h
      rw [Finset.disjoint_image hf_emb] at h_disj
      exact hxy_inter h_disj
    have h_bound := katona_arc_lemma_zero h2k hk I' h0_in h_inter'
    omega

lemma choose_bound_of_double_counting {n k f : ℕ} (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (h_ineq : n * f * k.factorial * (n - k).factorial ≤ k * n.factorial) :
    f ≤ Nat.choose (n - 1) (k - 1) := by
  have hn_pos : 0 < n := by omega
  have hk_pos : 0 < k := by omega
  have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hk_sub : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
  have h1 : n.factorial = n * (n - 1).factorial := by
    nth_rw 1 [← hn_sub]
    rw [Nat.factorial_succ, hn_sub]
  have h2 : k.factorial = k * (k - 1).factorial := by
    nth_rw 1 [← hk_sub]
    rw [Nat.factorial_succ, hk_sub]
  have h_left : n * f * k.factorial * (n - k).factorial =
      (n * k) * (f * (k - 1).factorial * (n - k).factorial) := by
    rw [h2]
    ring
  have h_right : k * n.factorial = (n * k) * (n - 1).factorial := by
    rw [h1]
    ring
  rw [h_left, h_right] at h_ineq
  have h_nk_pos : 0 < n * k := mul_pos hn_pos hk_pos
  have h_step : f * (k - 1).factorial * (n - k).factorial ≤ (n - 1).factorial :=
    Nat.le_of_mul_le_mul_left h_ineq h_nk_pos
  have h_choose := Nat.choose_mul_factorial_mul_factorial (n := n - 1) (k := k - 1) (by omega)
  have h_sub_eq : (n - 1) - (k - 1) = n - k := by omega
  rw [h_sub_eq] at h_choose
  have h_prod : f * (k - 1).factorial * (n - k).factorial ≤
      (n - 1).choose (k - 1) * (k - 1).factorial * (n - k).factorial := by
    rw [h_choose]
    exact h_step
  have h_cancel1 := Nat.le_of_mul_le_mul_right h_prod (Nat.factorial_pos (n - k))
  have h_cancel2 := Nat.le_of_mul_le_mul_right h_cancel1 (Nat.factorial_pos (k - 1))
  exact h_cancel2

section ErdosKoRado

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The cyclic arc in `α` under an equivalence `e : α ≃ ZMod n` starting at index `i`. -/
def arcOf (e : α ≃ ZMod n) (k : ℕ) (i : ZMod n) : Finset α :=
  (cyclicArc n k i).image e.symm

lemma mem_arcOf_iff {n k : ℕ} (e : α ≃ ZMod n) (i : ZMod n) (x : α) :
    x ∈ arcOf e k i ↔ e x ∈ cyclicArc n k i := by
  rw [arcOf, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp [hy]
  · intro h
    exact ⟨e x, h, e.symm_apply_apply x⟩

lemma arcOf_card {n k : ℕ} (e : α ≃ ZMod n) (i : ZMod n) (hkn : k ≤ n) (hn : 0 < n) :
    (arcOf e k i).card = k := by
  rw [arcOf, card_image_of_injective _ e.symm.injective]
  exact cyclicArc_card i hkn hn

lemma not_disjoint_arcOf_iff {n k : ℕ} (e : α ≃ ZMod n) (i j : ZMod n) :
    ¬ Disjoint (arcOf e k i) (arcOf e k j) ↔ ¬ Disjoint (cyclicArc n k i) (cyclicArc n k j) := by
  rw [arcOf, arcOf, Finset.disjoint_image e.symm.injective]

/-- Shift equivalence on `ZMod n` by subtracting `i`. -/
def shiftEquiv (n : ℕ) (i : ZMod n) : ZMod n ≃ ZMod n where
  toFun x := x - i
  invFun x := x + i
  left_inv x := sub_add_cancel x i
  right_inv x := add_sub_cancel_right x i

lemma arcOf_shift {n k : ℕ} (e : α ≃ ZMod n) (i : ZMod n) :
    arcOf (e.trans (shiftEquiv n i)) k 0 = arcOf e k i := by
  ext x
  rw [mem_arcOf_iff, mem_arcOf_iff]
  dsimp [shiftEquiv]
  rw [mem_cyclicArc_iff, mem_cyclicArc_iff]
  constructor
  · rintro ⟨j, hj, hj_eq⟩
    refine ⟨j, hj, ?_⟩
    linear_combination hj_eq
  · rintro ⟨j, hj, hj_eq⟩
    refine ⟨j, hj, ?_⟩
    linear_combination hj_eq

/-- Identification of `ZMod n` with `Fin n` via `val`. -/
def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun x := ⟨x.val, x.val_lt⟩
  invFun y := (y.1 : ZMod n)
  left_inv x := by
    dsimp
    exact ZMod.natCast_zmod_val x
  right_inv y := by
    ext
    dsimp
    exact ZMod.val_natCast_of_lt y.2

lemma finCongr_val {n m : ℕ} (h : n = m) (y : Fin n) :
    ((finCongr h y : Fin m) : ℕ) = y.1 := by
  subst h
  rfl

/-- Natural bijection from `α ≃ ZMod n` to `Numbering α`. -/
def equivToNumbering {n : ℕ} [NeZero n] (hn : Fintype.card α = n) (e : α ≃ ZMod n) :
    Numbering α :=
  e.trans ((zmodFinEquiv n).trans (finCongr hn.symm))

lemma equivToNumbering_apply {n : ℕ} [NeZero n] (hn : Fintype.card α = n) (e : α ≃ ZMod n) (x : α) :
    ((equivToNumbering hn e x : Fin (Fintype.card α)) : ℕ) = (e x).val := rfl

def equivToNumberingEquiv {n : ℕ} [NeZero n] (hn : Fintype.card α = n) :
    (α ≃ ZMod n) ≃ Numbering α where
  toFun := equivToNumbering hn
  invFun f := f.trans ((finCongr hn).trans (zmodFinEquiv n).symm)
  left_inv e := by
    ext x
    dsimp [equivToNumbering]
    simp
  right_inv f := by
    ext x
    dsimp [equivToNumbering]
    simp

lemma arcOf_zero_eq_iff_isPrefix {n k : ℕ} [NeZero n] (hn : Fintype.card α = n) (hkn : k ≤ n)
    (e : α ≃ ZMod n) (A : Finset α) (hA : A.card = k) :
    arcOf e k 0 = A ↔ Numbering.IsPrefix (equivToNumbering hn e) A := by
  constructor
  · intro heq x
    rw [← heq, mem_arcOf_iff]
    rw [mem_cyclicArc_zero_iff hkn (NeZero.pos n)]
    rw [arcOf_card e 0 hkn (NeZero.pos n)]
    rw [equivToNumbering_apply]
  · intro hp
    ext x
    rw [mem_arcOf_iff]
    rw [mem_cyclicArc_zero_iff hkn (NeZero.pos n)]
    rw [← equivToNumbering_apply hn e x]
    have h_card_eq : #A = k := hA
    have h_lt : (equivToNumbering hn e x : ℕ) < k ↔ equivToNumbering hn e x < #A := by
      rw [h_card_eq]
    rw [h_lt]
    exact (hp x).symm

lemma card_fiber_arcOf_zero {n k : ℕ} [NeZero n] (hn : Fintype.card α = n) (hkn : k ≤ n)
    (A : Finset α) (hA : A.card = k) :
    (Finset.filter (fun e : α ≃ ZMod n => arcOf e k 0 = A) Finset.univ).card =
      k.factorial * (n - k).factorial := by
  have h_filter : (Finset.filter (fun e : α ≃ ZMod n => arcOf e k 0 = A) Finset.univ) =
      (Numbering.prefixed A).map (equivToNumberingEquiv hn).symm.toEmbedding := by
    apply Finset.ext
    intro e
    simp only [mem_filter, mem_univ, true_and, mem_map, Numbering.mem_prefixed, Equiv.coe_toEmbedding]
    constructor
    · intro he
      refine ⟨equivToNumbering hn e, ?_, (equivToNumberingEquiv hn).left_inv e⟩
      rw [← arcOf_zero_eq_iff_isPrefix hn hkn e A hA]
      exact he
    · rintro ⟨f, hf, rfl⟩
      rw [arcOf_zero_eq_iff_isPrefix hn hkn _ A hA]
      have : equivToNumbering hn ((equivToNumberingEquiv hn).symm f) = f :=
        (equivToNumberingEquiv hn).right_inv f
      rw [this]
      exact hf
  rw [h_filter, card_map]
  rw [Numbering.card_prefixed]
  rw [hA, hn]

lemma card_fiber_arcOf {n k : ℕ} [NeZero n] (hn : Fintype.card α = n) (hkn : k ≤ n)
    (A : Finset α) (hA : A.card = k) (i : ZMod n) :
    (Finset.filter (fun e : α ≃ ZMod n => arcOf e k i = A) Finset.univ).card =
      k.factorial * (n - k).factorial := by
  let shift : (α ≃ ZMod n) ≃ (α ≃ ZMod n) := {
    toFun := fun e => e.trans (shiftEquiv n i)
    invFun := fun e => e.trans (shiftEquiv n (-i))
    left_inv := fun e => by
      ext x
      dsimp [shiftEquiv]
      ring
    right_inv := fun e => by
      ext x
      dsimp [shiftEquiv]
      ring
  }
  have h_map : (Finset.filter (fun e : α ≃ ZMod n => arcOf e k i = A) Finset.univ) =
      (Finset.filter (fun e : α ≃ ZMod n => arcOf e k 0 = A) Finset.univ).map shift.symm.toEmbedding := by
    apply Finset.ext
    intro e
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro he
      refine ⟨shift e, ?_, shift.left_inv e⟩
      dsimp [shift]
      rw [arcOf_shift]
      exact he
    · rintro ⟨e', he', rfl⟩
      dsimp [shift]
      have h_eq : (e'.trans (shiftEquiv n (-i))).trans (shiftEquiv n i) = e' := by
        ext x; dsimp [shiftEquiv]; ring
      rw [← arcOf_shift, h_eq]
      exact he'
  rw [h_map, card_map]
  exact card_fiber_arcOf_zero hn hkn A hA

/-- **Erdős–Ko–Rado Theorem (1961):**
Let `α` be a finite type of size `n` with `n ≥ 2k` and `k ≥ 1`.
If `ℱ` is an intersecting family of `k`-element subsets of `α`, then
`|ℱ| ≤ Nat.choose (n - 1) (k - 1)`. -/
theorem erdos_ko_rado {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) :
    F.card ≤ Nat.choose (n - 1) (k - 1) := by
  have hn_pos : 0 < n := by omega
  have : NeZero n := ⟨by omega⟩
  have hkn : k ≤ n := by omega
  have h_sum_e (e : α ≃ ZMod n) :
      (∑ i : ZMod n, (if arcOf e k i ∈ F then 1 else 0)) ≤ k := by
    have h_boole : (∑ i : ZMod n, (if arcOf e k i ∈ F then 1 else 0)) =
        (Finset.filter (fun i => arcOf e k i ∈ F) Finset.univ).card :=
      Finset.sum_boole (fun i => arcOf e k i ∈ F) Finset.univ
    rw [h_boole]
    let Ie : Finset (ZMod n) := Finset.filter (fun i => arcOf e k i ∈ F) Finset.univ
    have h_le : Ie.card ≤ k := by
      apply katona_arc_lemma h2k hk Ie
      intro i hi j hj
      rw [mem_filter] at hi hj
      have h_not_disj := h_inter (arcOf e k i) hi.2 (arcOf e k j) hj.2
      exact (not_disjoint_arcOf_iff e i j).mp h_not_disj
    exact h_le
  have h_card_equiv : Fintype.card (α ≃ ZMod n) = n.factorial := by
    have h1 : Fintype.card (α ≃ ZMod n) = Fintype.card (Numbering α) :=
      Fintype.card_congr (equivToNumberingEquiv hn)
    have h2 : Fintype.card (Numbering α) = (Fintype.card α).factorial :=
      Fintype.card_numbering
    rw [h1, h2, hn]
  have h_bound_upper : (∑ e : α ≃ ZMod n, ∑ i : ZMod n, (if arcOf e k i ∈ F then 1 else 0)) ≤
      k * n.factorial := by
    have h_sum_le : (∑ e : α ≃ ZMod n, ∑ i : ZMod n, (if arcOf e k i ∈ F then 1 else 0)) ≤
        ∑ e : α ≃ ZMod n, k := by
      apply Finset.sum_le_sum
      intro e _
      exact h_sum_e e
    have h_sum_k : (∑ e : α ≃ ZMod n, k) = k * n.factorial := by
      rw [Finset.sum_const, smul_eq_mul, card_univ, h_card_equiv, mul_comm]
    rw [h_sum_k] at h_sum_le
    exact h_sum_le
  have h_sum_lower : (∑ e : α ≃ ZMod n, ∑ i : ZMod n, (if arcOf e k i ∈ F then 1 else 0)) =
      n * F.card * k.factorial * (n - k).factorial := by
    rw [Finset.sum_comm]
    have h_term_i (i : ZMod n) :
        (∑ e : α ≃ ZMod n, (if arcOf e k i ∈ F then 1 else 0)) =
        F.card * (k.factorial * (n - k).factorial) := by
      have h_decomp (e : α ≃ ZMod n) :
          (if arcOf e k i ∈ F then 1 else 0) =
          ∑ A ∈ F, (if arcOf e k i = A then 1 else 0) := by
        have h_eq : (∑ A ∈ F, if arcOf e k i = A then 1 else 0) =
            ∑ A ∈ F, if A = arcOf e k i then 1 else 0 := by
          refine Finset.sum_congr rfl (fun A _ => ?_)
          simp only [eq_comm]
        rw [h_eq, Finset.sum_ite_eq' F (arcOf e k i) (fun _ => 1)]
      have h_sum_e_eq : (∑ e : α ≃ ZMod n, (if arcOf e k i ∈ F then 1 else 0)) =
          ∑ e : α ≃ ZMod n, ∑ A ∈ F, (if arcOf e k i = A then 1 else 0) := by
        refine Finset.sum_congr rfl (fun e _ => h_decomp e)
      rw [h_sum_e_eq, Finset.sum_comm]
      have h_term_A (A : Finset α) (hA : A ∈ F) :
          (∑ e : α ≃ ZMod n, (if arcOf e k i = A then 1 else 0)) =
          k.factorial * (n - k).factorial := by
        have h_boole : (∑ e : α ≃ ZMod n, (if arcOf e k i = A then 1 else 0)) =
            (Finset.filter (fun e => arcOf e k i = A) Finset.univ).card :=
          Finset.sum_boole (fun e => arcOf e k i = A) Finset.univ
        rw [h_boole]
        exact card_fiber_arcOf hn hkn A (hF_k A hA) i
      rw [Finset.sum_congr rfl h_term_A, Finset.sum_const, smul_eq_mul]
    have h_sum_all_i : (∑ i : ZMod n, ∑ e : α ≃ ZMod n, (if arcOf e k i ∈ F then 1 else 0)) =
        ∑ i : ZMod n, (F.card * (k.factorial * (n - k).factorial)) := by
      refine Finset.sum_congr rfl (fun i _ => h_term_i i)
    rw [h_sum_all_i, Finset.sum_const, smul_eq_mul, card_univ]
    rw [ZMod.card n]
    ring
  have h_ineq : n * F.card * k.factorial * (n - k).factorial ≤ k * n.factorial := by
    rw [← h_sum_lower]
    exact h_bound_upper
  exact choose_bound_of_double_counting hk h2k h_ineq

/-- **Erdős–Ko–Rado Theorem (Unbundled / Disjoint Pair Formulation):**
If a family `F` of `k`-element subsets of an `n`-element set has size strictly
greater than `Nat.choose (n - 1) (k - 1)` (with `n ≥ 2k`), then `F` must contain
at least two disjoint sets. -/
theorem erdos_ko_rado_disjoint_pair {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_card : Nat.choose (n - 1) (k - 1) < F.card) :
    ∃ A ∈ F, ∃ B ∈ F, Disjoint A B := by
  by_contra! h_all_inter
  have h_le := erdos_ko_rado hn hk h2k F hF_k (fun A hA B hB => h_all_inter A hA B hB)
  exact lt_irrefl _ (h_card.trans_le h_le)

/-- **Erdős–Ko–Rado Theorem (Powerset Formulation):**
Intersecting subfamily of `(Finset.univ : Finset α).powersetCard k`. -/
theorem erdos_ko_rado_powersetCard {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 1 ≤ k) (h2k : 2 * k ≤ n)
    (F : Finset (Finset α))
    (hF : F ⊆ (Finset.univ : Finset α).powersetCard k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) :
    F.card ≤ Nat.choose (n - 1) (k - 1) := by
  apply erdos_ko_rado hn hk h2k F
  · intro A hA
    have := hF hA
    rw [Finset.mem_powersetCard] at this
    exact this.2
  · exact h_inter

-- ============================================================================
-- Section 7: Star Families & Intersection Centers
-- ============================================================================

/-- A family `F` of sets is a star (canonically centered) if all sets share a common element `x`. -/
def IsStarFamily (F : Finset (Finset α)) : Prop :=
  ∃ x : α, ∀ A ∈ F, x ∈ A

/-- The full star family centered at `x` among all `k`-subsets of `α`. -/
def starFamily (x : α) (k : ℕ) : Finset (Finset α) :=
  ((Finset.univ : Finset α).powersetCard k).filter (fun A => x ∈ A)

/-- The cardinality of any full star family on an `n`-element set is `Nat.choose (n - 1) (k - 1)`. -/
lemma card_starFamily {n k : ℕ} (hn : Fintype.card α = n) (hk : 1 ≤ k) (hkn : k ≤ n) (x : α) :
    (starFamily x k).card = Nat.choose (n - 1) (k - 1) := by
  dsimp [starFamily]
  have h_filter : (filter (fun A => x ∈ A) ((Finset.univ : Finset α).powersetCard k)) =
      filter (fun A => {x} ⊆ A) ((Finset.univ : Finset α).powersetCard k) := by
    apply Finset.filter_congr
    intro A hA
    simp only [singleton_subset_iff]
  rw [h_filter]
  have h_sub : ({x} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
  have h_card_singleton : ({x} : Finset α).card = 1 := Finset.card_singleton x
  have h_card_le : ({x} : Finset α).card ≤ k := by rw [h_card_singleton]; exact hk
  have h_card := Finset.card_filter_powersetCard_subset ({x} : Finset α) Finset.univ k h_sub h_card_le
  rw [h_card]
  rw [Finset.card_univ, hn, h_card_singleton]

-- ============================================================================
-- Section 8: EKR Uniqueness Theorem (n > 2k)
-- ============================================================================

/-- **EKR equality/uniqueness case (following from Hilton--Milner 1967):**
    For $n > 2k$, every intersecting family of $k$-sets achieving the maximal cardinality
    $\binom{n-1}{k-1}$ is necessarily a star family. The case `k = 1` is elementary;
    for `k ≥ 2`, the strict gap follows from the Hilton--Milner bound. -/
theorem erdos_ko_rado_uniqueness {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 1 ≤ k) (h2k : 2 * k < n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (h_max : F.card = Nat.choose (n - 1) (k - 1)) :
    IsStarFamily F := by
  sorry

-- ============================================================================
-- Section 9: Hilton–Milner Bound (EKR Stability)
-- ============================================================================

/-- The Hilton–Milner extremal bound: $\binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$. -/
def hiltonMilnerBound (n k : ℕ) : ℕ :=
  Nat.choose (n - 1) (k - 1) - Nat.choose (n - k - 1) (k - 1) + 1

/-- The classical Hilton--Milner family generated by a center `x` and one exceptional
`k`-set `B` not containing `x`: the set `B`, together with all `k`-sets that contain `x`
and intersect `B`. -/
def hiltonMilnerFamily (x : α) (B : Finset α) (k : ℕ) : Finset (Finset α) :=
  insert B ((starFamily x k).filter fun A => ¬ Disjoint A B)

/-- Among the full `k`-star centered at `x`, the sets disjoint from an exceptional
`k`-set `B` are counted by `Nat.choose (n - k - 1) (k - 1)`. -/
lemma card_disjoint_starFamily {n k : ℕ} (hn : Fintype.card α = n) (hk : 1 ≤ k)
    (x : α) (B : Finset α) (hB : B.card = k) (hxB : x ∉ B) :
    ((starFamily x k).filter fun A => Disjoint A B).card =
      Nat.choose (n - k - 1) (k - 1) := by
  have hxmem : x ∈ (Finset.univ : Finset α) \ B := by simp [hxB]
  have h_filter :
      (starFamily x k).filter (fun A => Disjoint A B) =
        (((Finset.univ : Finset α) \ B).powersetCard k).filter (fun A => {x} ⊆ A) := by
    ext A
    rw [mem_filter, mem_filter, starFamily, mem_filter, mem_powersetCard, mem_powersetCard]
    simp only [singleton_subset_iff]
    constructor
    · rintro ⟨⟨⟨hAuniv, hAcard⟩, hxA⟩, hdisj⟩
      refine ⟨⟨?_, hAcard⟩, hxA⟩
      intro y hy
      exact mem_sdiff.mpr ⟨mem_univ y, fun hyB => Finset.disjoint_left.mp hdisj hy hyB⟩
    · rintro ⟨⟨hAsub, hAcard⟩, hxA⟩
      refine ⟨⟨⟨Finset.subset_univ A, hAcard⟩, hxA⟩, ?_⟩
      exact Finset.disjoint_left.mpr fun y hyA hyB => (mem_sdiff.mp (hAsub hyA)).2 hyB
  rw [h_filter]
  have hcard := Finset.card_filter_powersetCard_subset
    ({x} : Finset α) ((Finset.univ : Finset α) \ B) k
    (by simpa [singleton_subset_iff] using hxmem) (by simp [hk])
  rw [hcard, Finset.card_sdiff_of_subset (Finset.subset_univ B), Finset.card_univ, hn, hB,
    Finset.card_singleton]

/-- Exact cardinality of the classical Hilton--Milner family. -/
lemma card_hiltonMilnerFamily {n k : ℕ} (hn : Fintype.card α = n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (x : α) (B : Finset α)
    (hB : B.card = k) (hxB : x ∉ B) :
    (hiltonMilnerFamily x B k).card = hiltonMilnerBound n k := by
  have hB_not_mem : B ∉ (starFamily x k).filter (fun A => ¬ Disjoint A B) := by
    simp [starFamily, hxB]
  rw [hiltonMilnerFamily, card_insert_of_notMem hB_not_mem, hiltonMilnerBound]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := starFamily x k) (fun A : Finset α => Disjoint A B)
  have hstar := card_starFamily hn hk hkn x
  have hdisj := card_disjoint_starFamily hn hk x B hB hxB
  omega

/-- Every member of the classical Hilton--Milner family is a `k`-set. -/
lemma hiltonMilnerFamily_uniform {k : ℕ} (x : α) (B : Finset α) (hB : B.card = k) :
    ∀ A ∈ hiltonMilnerFamily x B k, A.card = k := by
  intro A hA
  rw [hiltonMilnerFamily, mem_insert] at hA
  rcases hA with rfl | hA
  · exact hB
  · have hstar := (mem_filter.mp hA).1
    rw [starFamily, mem_filter, mem_powersetCard] at hstar
    exact hstar.1.2

/-- The classical Hilton--Milner family is pairwise intersecting. -/
lemma hiltonMilnerFamily_intersecting {k : ℕ} (hk : 1 ≤ k) (x : α)
    (B : Finset α) (hB : B.card = k) :
    ∀ A ∈ hiltonMilnerFamily x B k, ∀ C ∈ hiltonMilnerFamily x B k,
      ¬ Disjoint A C := by
  intro A hA C hC
  rw [hiltonMilnerFamily, mem_insert] at hA hC
  rcases hA with rfl | hA <;> rcases hC with rfl | hC
  · rw [Finset.disjoint_self_iff_empty]
    intro h
    rw [h, card_empty] at hB
    omega
  · exact fun h => (mem_filter.mp hC).2 h.symm
  · exact (mem_filter.mp hA).2
  · have hAstar := (mem_filter.mp hA).1
    have hCstar := (mem_filter.mp hC).1
    rw [starFamily, mem_filter] at hAstar hCstar
    have hxA : x ∈ A := hAstar.2
    have hxC : x ∈ C := hCstar.2
    exact fun h => Finset.disjoint_left.mp h hxA hxC

/-- If `k ≥ 2` and the exceptional set omits the center, the classical Hilton--Milner
family has no common element. -/
lemma hiltonMilnerFamily_not_star {k : ℕ} (hk : 2 ≤ k) (x : α)
    (B : Finset α) (hB : B.card = k) (hxB : x ∉ B) :
    ¬ IsStarFamily (hiltonMilnerFamily x B k) := by
  rintro ⟨y, hy⟩
  by_cases hyB : y ∈ B
  · have hBerase : (B.erase y).card = k - 1 := by
      rw [card_erase_of_mem hyB, hB]
    let A := insert x (B.erase y)
    have hxerase : x ∉ B.erase y := fun h => hxB (erase_subset y B h)
    have hAcard : A.card = k := by
      dsimp [A]
      rw [card_insert_of_notMem hxerase, hBerase]
      omega
    have hAdisj : ¬ Disjoint A B := by
      have hne : (B.erase y).Nonempty := by
        rw [← card_pos, hBerase]
        omega
      obtain ⟨z, hz⟩ := hne
      have hzB : z ∈ B := (mem_erase.mp hz).2
      have hzy : z ≠ y := (mem_erase.mp hz).1
      intro hd
      exact Finset.disjoint_left.mp hd (by simp [A, hzB, hzy]) hzB
    have hAmem : A ∈ hiltonMilnerFamily x B k := by
      rw [hiltonMilnerFamily, mem_insert]
      right
      rw [mem_filter]
      exact ⟨by simp [starFamily, hAcard, A], hAdisj⟩
    have hyx : y ≠ x := fun h => hxB (h ▸ hyB)
    have hy_not_A : y ∉ A := by simp [A, hyx]
    exact hy_not_A (hy A hAmem)
  · exact hyB (hy B (by simp [hiltonMilnerFamily]))

/-- **Sharpness of the Hilton--Milner bound.** For every `2 ≤ k` and `2k < n`,
there is a uniform, pairwise-intersecting, non-star family whose cardinality is exactly
`hiltonMilnerBound n k`. This is the classical exceptional-set construction described
after Theorem 1 of Bulavka--Woodroofe (2026). -/
theorem exists_hiltonMilner_extremizer {n k : ℕ} (hn : Fintype.card α = n)
    (hk : 2 ≤ k) (h2k : 2 * k < n) :
    ∃ F : Finset (Finset α),
      (∀ A ∈ F, A.card = k) ∧
      (∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B) ∧
      ¬ IsStarFamily F ∧
      F.card = hiltonMilnerBound n k := by
  have hnpos : 0 < Fintype.card α := by omega
  let x : α := Classical.choice (Fintype.card_pos_iff.mp hnpos)
  have herase : ((Finset.univ : Finset α).erase x).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ x), card_univ, hn]
  have hkcard : k ≤ ((Finset.univ : Finset α).erase x).card := by omega
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hkcard
  have hxB : x ∉ B := fun hx => (mem_erase.mp (hBsub hx)).1 rfl
  refine ⟨hiltonMilnerFamily x B k, hiltonMilnerFamily_uniform x B hBcard,
    hiltonMilnerFamily_intersecting (by omega) x B hBcard,
    hiltonMilnerFamily_not_star hk x B hBcard hxB, ?_⟩
  exact card_hiltonMilnerFamily hn (by omega) (by omega) x B hBcard hxB

/-- **Hilton–Milner Theorem (1967):**
    Let $n > 2k$ and $k \ge 2$. If $\mathcal{F}$ is an intersecting family of $k$-element subsets
    of an $n$-element universe that is NOT a star family, then
    $|\mathcal{F}| \le \binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$. -/
theorem hilton_milner_stability {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 2 ≤ k) (h2k : 2 * k < n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (h_not_star : ¬ IsStarFamily F) :
    F.card ≤ hiltonMilnerBound n k := by
  sorry

end ErdosKoRado

#print axioms erdos_ko_rado
