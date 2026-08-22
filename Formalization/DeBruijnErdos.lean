import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.deprecated false

namespace DeBruijnErdos

variable {α : Type*} [DecidableEq α]

/-- A finite linear space consists of a set of points `P : Finset α` and a set of lines
`L : Finset (Finset α)` satisfying:
1. Every line is a subset of `P`.
2. Every line contains at least 2 points.
3. Any two distinct points lie on a unique line.
4. Non-collinearity: no single line contains all points `P`.
5. Non-degeneracy: there are at least 3 points. -/
structure LinearSpace (P : Finset α) (L : Finset (Finset α)) : Prop where
  line_subset : ∀ l ∈ L, l ⊆ P
  line_card_ge_two : ∀ l ∈ L, 2 ≤ l.card
  unique_line : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ∃! l ∈ L, u ∈ l ∧ v ∈ l
  non_collinear : ∀ l ∈ L, ¬ P ⊆ l
  three_le_card : 3 ≤ P.card

/-- The degree of a point `p`: the number of lines containing `p`. -/
def pointDegree (L : Finset (Finset α)) (p : α) : ℕ :=
  (L.filter (fun l => p ∈ l)).card

lemma pointDegree_le_card (L : Finset (Finset α)) (p : α) :
    pointDegree L p ≤ L.card :=
  Finset.card_filter_le L _

lemma card_filter_not_mem (L : Finset (Finset α)) (p : α) :
    (L.filter (fun l => p ∉ l)).card = L.card - pointDegree L p := by
  have h_disj : Disjoint (L.filter (fun l => p ∈ l)) (L.filter (fun l => p ∉ l)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    exact hx2.2 hx1.2
  have h_union : L = (L.filter (fun l => p ∈ l)) ∪ (L.filter (fun l => p ∉ l)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      by_cases hp : p ∈ x
      · exact Or.inl ⟨hx, hp⟩
      · exact Or.inr ⟨hx, hp⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have h_card : L.card = pointDegree L p + (L.filter (fun l => p ∉ l)).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
    rfl
  omega

lemma exists_line_not_mem {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) {p : α} (hp : p ∈ P) :
    ∃ l ∈ L, p ∉ l := by
  by_contra h_all
  have h_all' : ∀ l ∈ L, p ∈ l := by
    intro l hl
    by_contra h_not
    exact h_all ⟨l, hl, h_not⟩
  have h_diff_card : (P.erase p).card = P.card - 1 := Finset.card_erase_of_mem hp
  have h_diff_ge_2 : 2 ≤ (P.erase p).card := by
    have := h.three_le_card
    omega
  have h_pos1 : 0 < (P.erase p).card := by omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp h_pos1
  have hu_mem_P : u ∈ P := (Finset.mem_erase.mp hu).2
  have hu_ne_p : u ≠ p := (Finset.mem_erase.mp hu).1
  have h_erase2_card : ((P.erase p).erase u).card = (P.erase p).card - 1 :=
    Finset.card_erase_of_mem hu
  have h_pos2 : 0 < ((P.erase p).erase u).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h_pos2
  have hv_erase : v ∈ P.erase p := (Finset.mem_erase.mp hv).2
  have hv_ne_u : v ≠ u := (Finset.mem_erase.mp hv).1
  have hv_mem_P : v ∈ P := (Finset.mem_erase.mp hv_erase).2
  have hv_ne_p : v ≠ p := (Finset.mem_erase.mp hv_erase).1
  have h_ne_uv : u ≠ v := hv_ne_u.symm
  obtain ⟨l1, ⟨hl1_L, hu_l1, hv_l1⟩, -⟩ := h.unique_line u hu_mem_P v hv_mem_P h_ne_uv
  have hp_l1 : p ∈ l1 := h_all' l1 hl1_L
  have h_not_sub : ¬ P ⊆ l1 := h.non_collinear l1 hl1_L
  obtain ⟨w, hw_P, hw_nl1⟩ := Finset.not_subset.mp h_not_sub
  have hw_ne_p : w ≠ p := by
    rintro rfl
    exact hw_nl1 hp_l1
  have hw_ne_u : w ≠ u := by
    rintro rfl
    exact hw_nl1 hu_l1
  have h_ne_uw : u ≠ w := hw_ne_u.symm
  obtain ⟨l2, ⟨hl2_L, hu_l2, hw_l2⟩, -⟩ := h.unique_line u hu_mem_P w hw_P h_ne_uw
  have hp_l2 : p ∈ l2 := h_all' l2 hl2_L
  obtain ⟨l_pu, ⟨-, -, -⟩, hl_pu_uniq⟩ := h.unique_line p hp u hu_mem_P (Ne.symm hu_ne_p)
  have hl1_eq : l1 = l_pu := hl_pu_uniq l1 ⟨hl1_L, hp_l1, hu_l1⟩
  have hl2_eq : l2 = l_pu := hl_pu_uniq l2 ⟨hl2_L, hp_l2, hu_l2⟩
  have hl1_eq_l2 : l1 = l2 := hl1_eq.trans hl2_eq.symm
  have hw_in_l1 : w ∈ l1 := by
    rw [hl1_eq_l2]
    exact hw_l2
  exact hw_nl1 hw_in_l1

noncomputable def lineThrough {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) (p q : α) (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) : Finset α :=
  Classical.choose (ExistsUnique.exists (h.unique_line p hp q hq hne))

lemma lineThrough_mem {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) (p q : α) (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    lineThrough h p q hp hq hne ∈ L ∧
    p ∈ lineThrough h p q hp hq hne ∧
    q ∈ lineThrough h p q hp hq hne :=
  Classical.choose_spec (ExistsUnique.exists (h.unique_line p hp q hq hne))

lemma card_line_le_pointDegree {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) {l : Finset α} (hl : l ∈ L) {p : α} (hp : p ∈ P) (hp_not : p ∉ l) :
    l.card ≤ pointDegree L p := by
  let f : α → Finset α := fun q =>
    if hq : q ∈ l then
      lineThrough h p q hp (h.line_subset l hl hq) (fun heq => hp_not (heq ▸ hq))
    else ∅
  have h_img_sub : l.image f ⊆ L.filter (fun k => p ∈ k) := by
    intro k hk
    obtain ⟨q, hq_l, rfl⟩ := Finset.mem_image.mp hk
    dsimp [f]
    rw [dif_pos hq_l]
    have h_spec := lineThrough_mem h p q hp (h.line_subset l hl hq_l)
      (fun heq => hp_not (heq ▸ hq_l))
    exact Finset.mem_filter.mpr ⟨h_spec.1, h_spec.2.1⟩
  have h_inj : ∀ q1 ∈ l, ∀ q2 ∈ l, f q1 = f q2 → q1 = q2 := by
    intro q1 hq1 q2 hq2 h_eq
    dsimp [f] at h_eq
    rw [dif_pos hq1, dif_pos hq2] at h_eq
    by_contra h_ne
    have hq1_P : q1 ∈ P := h.line_subset l hl hq1
    have hq2_P : q2 ∈ P := h.line_subset l hl hq2
    let K := lineThrough h p q1 hp hq1_P (fun heq => hp_not (heq ▸ hq1))
    have hK1 := lineThrough_mem h p q1 hp hq1_P (fun heq => hp_not (heq ▸ hq1))
    have hK2 : K ∈ L ∧ p ∈ K ∧ q2 ∈ K := by
      have hK_eq : K = lineThrough h p q2 hp hq2_P (fun heq => hp_not (heq ▸ hq2)) := h_eq
      rw [hK_eq]
      exact lineThrough_mem h p q2 hp hq2_P (fun heq => hp_not (heq ▸ hq2))
    obtain ⟨l_q1q2, ⟨-, -, -⟩, hl_uniq⟩ := h.unique_line q1 hq1_P q2 hq2_P h_ne
    have hl_eq : l = l_q1q2 := hl_uniq l ⟨hl, hq1, hq2⟩
    have hK_eq : K = l_q1q2 := hl_uniq K ⟨hK1.1, hK1.2.2, hK2.2.2⟩
    have hl_eq_K : l = K := hl_eq.trans hK_eq.symm
    have hp_in_l : p ∈ l := by
      rw [hl_eq_K]
      exact hK1.2.1
    exact hp_not hp_in_l
  have h_card_eq : (l.image f).card = l.card :=
    Finset.card_image_of_injOn (fun q1 hq1 q2 hq2 => h_inj q1 hq1 q2 hq2)
  rw [← h_card_eq]
  exact Finset.card_le_card h_img_sub

lemma two_le_pointDegree {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) {p : α} (hp : p ∈ P) :
    2 ≤ pointDegree L p := by
  obtain ⟨l, hl_L, hp_nl⟩ := exists_line_not_mem h hp
  have h2 : 2 ≤ l.card := h.line_card_ge_two l hl_L
  have h_le : l.card ≤ pointDegree L p := card_line_le_pointDegree h hl_L hp hp_nl
  exact h2.trans h_le

lemma card_line_lt_card_points {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) {l : Finset α} (hl : l ∈ L) :
    l.card < P.card := by
  have h_sub : l ⊆ P := h.line_subset l hl
  have h_not_sub : ¬ P ⊆ l := h.non_collinear l hl
  have h_ne : l ≠ P := by
    rintro rfl
    exact h_not_sub (Finset.Subset.refl _)
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, h_ne⟩)

lemma double_sum_swap (P : Finset α) (L : Finset (Finset α)) (g : α → Finset α → ℝ) :
    ∑ l ∈ L, ∑ p ∈ P \ l, g p l = ∑ p ∈ P, ∑ l ∈ L.filter (fun k => p ∉ k), g p l := by
  have hl (l : Finset α) : ∑ p ∈ P \ l, g p l = ∑ p ∈ P, if p ∉ l then g p l else 0 := by
    have : P \ l = P.filter (fun p => p ∉ l) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_filter]
    rw [this, Finset.sum_filter]
  have hp (p : α) : ∑ l ∈ L.filter (fun k => p ∉ k), g p l = ∑ l ∈ L, if p ∉ l then g p l else 0 := by
    rw [Finset.sum_filter]
  simp_rw [hl, hp]
  exact Finset.sum_comm

lemma sum_lines_eq_card_lines {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) :
    ∑ l ∈ L, ∑ p ∈ P \ l, (1 / ((P.card : ℝ) - (l.card : ℝ))) = (L.card : ℝ) := by
  have h_inner (l : Finset α) (hl : l ∈ L) :
      ∑ p ∈ P \ l, (1 / ((P.card : ℝ) - (l.card : ℝ))) = 1 := by
    rw [Finset.sum_const]
    have h_sub : l ⊆ P := h.line_subset l hl
    have h_diff_card : (P \ l).card = P.card - l.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h_sub]
    have h_lt : l.card < P.card := card_line_lt_card_points h hl
    have h_pos : (P.card : ℝ) - (l.card : ℝ) ≠ 0 := by
      have : (l.card : ℝ) < (P.card : ℝ) := Nat.cast_lt.mpr h_lt
      linarith
    have h_cast : ((P \ l).card : ℝ) = (P.card : ℝ) - (l.card : ℝ) := by
      rw [h_diff_card]
      have : l.card ≤ P.card := Nat.le_of_lt h_lt
      exact Nat.cast_sub this
    rw [nsmul_eq_mul, h_cast, mul_one_div, div_self h_pos]
  have h_outer : ∑ l ∈ L, ∑ p ∈ P \ l, (1 / ((P.card : ℝ) - (l.card : ℝ))) =
      ∑ l ∈ L, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro l hl
    exact h_inner l hl
  rw [h_outer, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma sum_points_eval (P : Finset α) (L : Finset (Finset α)) :
    ∑ p ∈ P, ∑ l ∈ L.filter (fun k => p ∉ k), (1 / ((P.card : ℝ) - (pointDegree L p : ℝ))) =
    ∑ p ∈ P, (((L.card : ℝ) - (pointDegree L p : ℝ)) / ((P.card : ℝ) - (pointDegree L p : ℝ))) := by
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_const, nsmul_eq_mul]
  have h_card := card_filter_not_mem L p
  have h_cast : ((L.filter (fun l => p ∉ l)).card : ℝ) = (L.card : ℝ) - (pointDegree L p : ℝ) := by
    rw [h_card]
    have h_le : pointDegree L p ≤ L.card := pointDegree_le_card L p
    exact Nat.cast_sub h_le
  rw [h_cast, mul_one_div]

lemma inv_sub_le_inv_sub_of_le {n m d c : ℕ} (h_m_lt_n : m < n) (h_d_le_m : d ≤ m)
    (h_c_le_d : c ≤ d) :
    1 / ((n : ℝ) - (c : ℝ)) ≤ 1 / ((n : ℝ) - (d : ℝ)) := by
  have hd_lt_n : d < n := lt_of_le_of_lt h_d_le_m h_m_lt_n
  have hc_lt_n : c < n := lt_of_le_of_lt h_c_le_d hd_lt_n
  have h_pos_d : 0 < (n : ℝ) - (d : ℝ) := by
    have : (d : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hd_lt_n
    linarith
  have h_pos_c : 0 < (n : ℝ) - (c : ℝ) := by
    have : (c : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hc_lt_n
    linarith
  have h_le : (n : ℝ) - (d : ℝ) ≤ (n : ℝ) - (c : ℝ) := by
    have : (c : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr h_c_le_d
    linarith
  exact one_div_le_one_div_of_le h_pos_d h_le

lemma card_lines_le_sum_frac {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) (h_lt : L.card < P.card) :
    (L.card : ℝ) ≤ ∑ p ∈ P, (((L.card : ℝ) - (pointDegree L p : ℝ)) / ((P.card : ℝ) - (pointDegree L p : ℝ))) := by
  have h_sum_le : ∑ l ∈ L, ∑ p ∈ P \ l, (1 / ((P.card : ℝ) - (l.card : ℝ))) ≤
      ∑ l ∈ L, ∑ p ∈ P \ l, (1 / ((P.card : ℝ) - (pointDegree L p : ℝ))) := by
    apply Finset.sum_le_sum
    intro l hl
    apply Finset.sum_le_sum
    intro p hp_diff
    have hp_P : p ∈ P := (Finset.mem_sdiff.mp hp_diff).1
    have hp_nl : p ∉ l := (Finset.mem_sdiff.mp hp_diff).2
    have h_c_le_d : l.card ≤ pointDegree L p := card_line_le_pointDegree h hl hp_P hp_nl
    have h_d_le_m : pointDegree L p ≤ L.card := pointDegree_le_card L p
    exact inv_sub_le_inv_sub_of_le h_lt h_d_le_m h_c_le_d
  rw [sum_lines_eq_card_lines h] at h_sum_le
  rw [double_sum_swap] at h_sum_le
  rw [sum_points_eval] at h_sum_le
  exact h_sum_le

lemma frac_sub_lt_frac {m n d : ℕ} (h_lt : m < n) (h_d_le_m : d ≤ m) (h_d_pos : 1 ≤ d) :
    ((m : ℝ) - (d : ℝ)) / ((n : ℝ) - (d : ℝ)) < (m : ℝ) / (n : ℝ) := by
  have hd_lt_n : d < n := lt_of_le_of_lt h_d_le_m h_lt
  have h_d_pos_r : 0 < (d : ℝ) := Nat.cast_pos.mpr h_d_pos
  have h_m_lt_n_r : (m : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h_lt
  have h_n_pos_r : 0 < (n : ℝ) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le m) h_lt
    exact Nat.cast_pos.mpr this
  have h_denom_pos : 0 < (n : ℝ) - (d : ℝ) := by
    have : (d : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hd_lt_n
    linarith
  rw [div_lt_div_iff₀ h_denom_pos h_n_pos_r]
  have h_mul1 : ((m : ℝ) - (d : ℝ)) * (n : ℝ) = (m : ℝ) * (n : ℝ) - (d : ℝ) * (n : ℝ) := by ring
  have h_mul2 : (m : ℝ) * ((n : ℝ) - (d : ℝ)) = (m : ℝ) * (n : ℝ) - (m : ℝ) * (d : ℝ) := by ring
  rw [h_mul1, h_mul2]
  have : (m : ℝ) * (d : ℝ) < (d : ℝ) * (n : ℝ) := by
    have : (m : ℝ) * (d : ℝ) < (n : ℝ) * (d : ℝ) := mul_lt_mul_of_pos_right h_m_lt_n_r h_d_pos_r
    linarith
  linarith

lemma sum_frac_lt_card_lines {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) (h_lt : L.card < P.card) :
    ∑ p ∈ P, (((L.card : ℝ) - (pointDegree L p : ℝ)) / ((P.card : ℝ) - (pointDegree L p : ℝ))) < (L.card : ℝ) := by
  have hP_nonempty : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_emp
    have : P.card = 0 := Finset.card_eq_zero.mpr h_emp
    have := h.three_le_card
    omega
  have h_lt_each : ∀ p ∈ P,
      (((L.card : ℝ) - (pointDegree L p : ℝ)) / ((P.card : ℝ) - (pointDegree L p : ℝ))) <
      (L.card : ℝ) / (P.card : ℝ) := by
    intro p hp
    have h_d_le_m : pointDegree L p ≤ L.card := pointDegree_le_card L p
    have h_deg_ge_2 : 2 ≤ pointDegree L p := two_le_pointDegree h hp
    have h_d_pos : 1 ≤ pointDegree L p := by omega
    exact frac_sub_lt_frac h_lt h_d_le_m h_d_pos
  have h_sum_lt := Finset.sum_lt_sum_of_nonempty hP_nonempty h_lt_each
  have h_const : ∑ p ∈ P, ((L.card : ℝ) / (P.card : ℝ)) = (L.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hP_pos : (P.card : ℝ) ≠ 0 := by
      have : 0 < P.card := by have := h.three_le_card; omega
      exact Nat.cast_ne_zero.mpr (ne_of_gt this)
    rw [mul_div_cancel₀ (L.card : ℝ) hP_pos]
  rw [h_const] at h_sum_lt
  exact h_sum_lt

/-- **De Bruijn–Erdős Theorem on Incidence Geometry** (De Bruijn & Erdős, 1948):
In any finite non-collinear linear space with at least 3 points, the number of lines
is at least the number of points: `P.card ≤ L.card`. -/
theorem de_bruijn_erdos {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) : P.card ≤ L.card := by
  by_contra h_not_le
  have h_lt : L.card < P.card := not_le.mp h_not_le
  have h_le := card_lines_le_sum_frac h h_lt
  have h_strict := sum_frac_lt_card_lines h h_lt
  exact lt_irrefl (L.card : ℝ) (h_le.trans_lt h_strict)

/-- Unbundled formulation of the De Bruijn–Erdős Theorem. -/
theorem de_bruijn_erdos' {P : Finset α} {L : Finset (Finset α)}
    (h_line_sub : ∀ l ∈ L, l ⊆ P)
    (h_line_ge_two : ∀ l ∈ L, 2 ≤ l.card)
    (h_uniq : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ∃! l ∈ L, u ∈ l ∧ v ∈ l)
    (h_non_collinear : ∀ l ∈ L, ¬ P ⊆ l)
    (h_card : 3 ≤ P.card) :
    P.card ≤ L.card :=
  de_bruijn_erdos ⟨h_line_sub, h_line_ge_two, h_uniq, h_non_collinear, h_card⟩

-- ============================================================================
-- Near-Pencil Equality Witness Construction
-- ============================================================================

/-- The lines of a near-pencil configuration on point set `P` with apex `p₀ ∈ P`:
one long line `P \ {p₀}` containing all other points, and `|P| - 1` lines of size 2
connecting `p₀` to each other point. -/
def nearPencilLines (P : Finset α) (p₀ : α) : Finset (Finset α) :=
  insert (P.erase p₀) ((P.erase p₀).image (fun q => {p₀, q}))

lemma mem_nearPencilLines_iff {P : Finset α} {p₀ : α} {l : Finset α} :
    l ∈ nearPencilLines P p₀ ↔ l = P.erase p₀ ∨ ∃ q ∈ P.erase p₀, l = {p₀, q} := by
  simp only [nearPencilLines, mem_insert, mem_image, eq_comm]

lemma nearPencil_card (P : Finset α) (p₀ : α) (hp₀ : p₀ ∈ P) (hcard : 3 ≤ P.card) :
    (nearPencilLines P p₀).card = P.card := by
  have h_not_mem : P.erase p₀ ∉ (P.erase p₀).image (fun q => ({p₀, q} : Finset α)) := by
    intro h_mem
    rcases mem_image.mp h_mem with ⟨q, hq, heq⟩
    have hp₀_in : p₀ ∈ ({p₀, q} : Finset α) := mem_insert_self p₀ {q}
    have hp₀_notin : p₀ ∉ P.erase p₀ := by simp
    rw [heq] at hp₀_in
    exact hp₀_notin hp₀_in
  have h_inj : ∀ q1 ∈ P.erase p₀, ∀ q2 ∈ P.erase p₀, ({p₀, q1} : Finset α) = {p₀, q2} → q1 = q2 := by
    intro q1 hq1 q2 hq2 heq
    have hq1_ne : q1 ≠ p₀ := (mem_erase.mp hq1).1
    have hq1_in : q1 ∈ ({p₀, q2} : Finset α) := by
      rw [← heq]
      exact mem_insert_of_mem (mem_singleton_self q1)
    simp only [mem_insert, mem_singleton] at hq1_in
    cases hq1_in with
    | inl h => exact False.elim (hq1_ne h)
    | inr h => exact h
  rw [nearPencilLines, card_insert_of_notMem h_not_mem,
      card_image_of_injOn h_inj, card_erase_of_mem hp₀]
  omega

lemma nearPencil_linearSpace (P : Finset α) (p₀ : α) (hp₀ : p₀ ∈ P) (hcard : 3 ≤ P.card) :
    LinearSpace P (nearPencilLines P p₀) where
  line_subset := by
    intro l hl
    rw [mem_nearPencilLines_iff] at hl
    rcases hl with rfl | ⟨q, hq, rfl⟩
    · exact erase_subset p₀ P
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hp₀
      · exact (mem_erase.mp hq).2
  line_card_ge_two := by
    intro l hl
    rw [mem_nearPencilLines_iff] at hl
    rcases hl with rfl | ⟨q, hq, rfl⟩
    · rw [card_erase_of_mem hp₀]
      omega
    · have hq_ne : p₀ ≠ q := (mem_erase.mp hq).1.symm
      rw [card_pair hq_ne]
  unique_line := by
    intro u hu v hv hne
    by_cases hu_p : u = p₀
    · have hu_p_eq : u = p₀ := hu_p
      have hv_ne_p : v ≠ p₀ := by
        rintro rfl
        exact hne hu_p_eq
      have hv_erase : v ∈ P.erase p₀ := mem_erase.mpr ⟨hv_ne_p, hv⟩
      refine ⟨{p₀, v}, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · rw [mem_nearPencilLines_iff]
          exact Or.inr ⟨v, hv_erase, rfl⟩
        · rw [hu_p_eq]
          exact mem_insert_self p₀ {v}
        · exact mem_insert_of_mem (mem_singleton_self v)
      · intro l' ⟨hl'_in, h_u_l', h_v_l'⟩
        rw [hu_p_eq] at h_u_l'
        rw [mem_nearPencilLines_iff] at hl'_in
        rcases hl'_in with rfl | ⟨q, hq, rfl⟩
        · have hp₀_notin : p₀ ∉ P.erase p₀ := by simp
          exact False.elim (hp₀_notin h_u_l')
        · have : v = p₀ ∨ v = q := by
            simpa only [mem_insert, mem_singleton] using h_v_l'
          rcases this with rfl | rfl
          · exact False.elim (hv_ne_p rfl)
          · rfl
    · by_cases hv_p : v = p₀
      · have hv_p_eq : v = p₀ := hv_p
        have hu_erase : u ∈ P.erase p₀ := mem_erase.mpr ⟨hu_p, hu⟩
        refine ⟨{p₀, u}, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · rw [mem_nearPencilLines_iff]
            exact Or.inr ⟨u, hu_erase, rfl⟩
          · exact mem_insert_of_mem (mem_singleton_self u)
          · rw [hv_p_eq]
            exact mem_insert_self p₀ {u}
        · intro l' ⟨hl'_in, h_u_l', h_p₀_l'⟩
          rw [hv_p_eq] at h_p₀_l'
          rw [mem_nearPencilLines_iff] at hl'_in
          rcases hl'_in with rfl | ⟨q, hq, rfl⟩
          · have hp₀_notin : p₀ ∉ P.erase p₀ := by simp
            exact False.elim (hp₀_notin h_p₀_l')
          · have : u = p₀ ∨ u = q := by
              simpa only [mem_insert, mem_singleton] using h_u_l'
            rcases this with rfl | rfl
            · exact False.elim (hu_p rfl)
            · rfl
      · have hu_erase : u ∈ P.erase p₀ := mem_erase.mpr ⟨hu_p, hu⟩
        have hv_erase : v ∈ P.erase p₀ := mem_erase.mpr ⟨hv_p, hv⟩
        refine ⟨P.erase p₀, ?_, ?_⟩
        · refine ⟨?_, hu_erase, hv_erase⟩
          rw [mem_nearPencilLines_iff]
          exact Or.inl rfl
        · intro l' ⟨hl'_in, h_u_l', h_v_l'⟩
          rw [mem_nearPencilLines_iff] at hl'_in
          rcases hl'_in with rfl | ⟨q, hq, rfl⟩
          · rfl
          · have hu_cases : u = p₀ ∨ u = q := by
              simpa only [mem_insert, mem_singleton] using h_u_l'
            have hv_cases : v = p₀ ∨ v = q := by
              simpa only [mem_insert, mem_singleton] using h_v_l'
            rcases hu_cases with rfl | rfl
            · exact False.elim (hu_p rfl)
            · rcases hv_cases with rfl | rfl
              · exact False.elim (hv_p rfl)
              · exact False.elim (hne rfl)
  non_collinear := by
    intro l hl
    rw [mem_nearPencilLines_iff] at hl
    rcases hl with rfl | ⟨q, hq, rfl⟩
    · intro h_sub
      have hp₀_notin : p₀ ∉ P.erase p₀ := by simp
      exact hp₀_notin (h_sub hp₀)
    · intro h_sub
      have h_card_le := card_le_card h_sub
      have hq_ne : p₀ ≠ q := (mem_erase.mp hq).1.symm
      rw [card_pair hq_ne] at h_card_le
      omega
  three_le_card := hcard

/-- **Tightness of the De Bruijn–Erdős Theorem**:
For any finite set of points `P` with `|P| ≥ 3` and any point `p₀ ∈ P`,
the near-pencil linear space on `P` with apex `p₀` achieves equality: `|P| = |L|`. -/
theorem de_bruijn_erdos_tight (P : Finset α) (p₀ : α) (hp₀ : p₀ ∈ P) (hcard : 3 ≤ P.card) :
    ∃ L : Finset (Finset α), LinearSpace P L ∧ L.card = P.card :=
  ⟨nearPencilLines P p₀, nearPencil_linearSpace P p₀ hp₀ hcard, nearPencil_card P p₀ hp₀ hcard⟩

#print axioms de_bruijn_erdos
#print axioms de_bruijn_erdos'
#print axioms de_bruijn_erdos_tight

end DeBruijnErdos

