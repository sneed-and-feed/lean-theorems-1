import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

/-- Sub-lemma 1: For any i ≠ j, the ordering conditions for A_i before B_i and A_j before B_j are mutually exclusive. -/
lemma bollobas_events_disjoint {α : Type*} [DecidableEq α] [Preorder α] {m : ℕ}
    (A B : Fin m → Finset α)
    (h_inter : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j))
    (i j : Fin m) (hij : i ≠ j) (π : Equiv.Perm α)
    (hi : ∀ a ∈ A i, ∀ b ∈ B i, π a < π b)
    (hj : ∀ a ∈ A j, ∀ b ∈ B j, π a < π b) :
    False := by
  obtain ⟨x, hxA, hxB⟩ := Finset.not_disjoint_iff.mp (h_inter i j hij)
  obtain ⟨y, hyA, hyB⟩ := Finset.not_disjoint_iff.mp (h_inter j i hij.symm)
  exact lt_asymm (hi x hxA y hyB) (hj y hyA x hxB)

lemma choose_mul_eq (a b : ℕ) (ha : 1 ≤ a) :
    ((a + b).choose a : ℝ) * a = (a + b : ℝ) * (((a - 1) + b).choose (a - 1) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (a - 1 + b) (a - 1)
  rw [Nat.sub_add_cancel ha, show a - 1 + b + 1 = a + b by omega] at h
  exact_mod_cast h.symm

lemma sum_term_eq (a b : ℕ) (ha : 1 ≤ a) :
    (a : ℝ) * (1 / (((a - 1) + b).choose (a - 1) : ℝ)) = (a + b : ℝ) * (1 / ((a + b).choose a : ℝ)) := by
  have h1 : (0 : ℝ) < ((a - 1) + b).choose (a - 1) := by exact_mod_cast Nat.choose_pos (by omega)
  have h2 : (0 : ℝ) < (a + b).choose a := by exact_mod_cast Nat.choose_pos (by omega)
  rw [mul_one_div, mul_one_div, div_eq_div_iff h1.ne.symm h2.ne.symm, mul_comm (a:ℝ)]
  exact choose_mul_eq a b ha

lemma sum_split_3 {α : Type*} [DecidableEq α] (X s t : Finset α)
    (h_disj : Disjoint s t) (hs : s ⊆ X) (ht : t ⊆ X) (f : α → ℝ) :
    (∑ x ∈ X, f x) = (∑ x ∈ s, f x) + (∑ x ∈ t, f x) + (∑ x ∈ X \ (s ∪ t), f x) := by
  rw [← Finset.sum_union h_disj, ← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.union_subset hs ht)]

lemma sum_single_pair_step {α : Type*} [DecidableEq α] (X A B : Finset α)
    (h_disj : Disjoint A B) (hA : A ⊆ X) (hB : B ⊆ X) (ha : 1 ≤ A.card) :
    (∑ x ∈ X, (if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ))) =
      (X.card : ℝ) * (1 / ((A.card + B.card).choose A.card : ℝ)) := by
  have h_split := sum_split_3 X A B h_disj hA hB
    (fun x => if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ))
  rw [h_split]
  have h_sum_B : (∑ x ∈ B, (if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp only [hx, ite_true]
  have h_sum_diff : (∑ x ∈ X \ (A ∪ B), (if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ))) =
      ((X \ (A ∪ B)).card : ℝ) * (1 / ((A.card + B.card).choose A.card : ℝ)) := by
    have h_const : ∀ x ∈ X \ (A ∪ B), (if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ)) =
        1 / ((A.card + B.card).choose A.card : ℝ) := by
      intro x hx
      have hx_notB : x ∉ B := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right A h)
      have hx_notA : x ∉ A := fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left B h)
      simp only [hx_notB, ite_false]
      rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_right.mpr hx_notA)]
    rw [Finset.sum_congr rfl h_const, Finset.sum_const, nsmul_eq_mul]
  have h_sum_A : (∑ x ∈ A, (if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ))) =
      (A.card + B.card : ℝ) * (1 / ((A.card + B.card).choose A.card : ℝ)) := by
    have h_const : ∀ x ∈ A, (if x ∈ B then (0 : ℝ) else 1 / (((A \ {x}).card + B.card).choose (A \ {x}).card : ℝ)) =
        1 / (((A.card - 1) + B.card).choose (A.card - 1) : ℝ) := by
      intro x hx
      have hx_notB : x ∉ B := Finset.disjoint_right.mp h_disj.symm hx
      simp only [hx_notB, ite_false]
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hx]
    rw [Finset.sum_congr rfl h_const, Finset.sum_const, nsmul_eq_mul]
    exact sum_term_eq A.card B.card ha
  rw [h_sum_A, h_sum_B, h_sum_diff, add_zero, ← add_mul]
  have h_union_sub : A ∪ B ⊆ X := Finset.union_subset hA hB
  have h_card_union : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint h_disj
  have h_card_diff : (X \ (A ∪ B)).card = X.card - (A.card + B.card) := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h_union_sub, h_card_union]
  have h_le : A.card + B.card ≤ X.card := by
    rw [← h_card_union]
    exact Finset.card_le_card h_union_sub
  have h_add : (A.card + B.card : ℝ) + ((X \ (A ∪ B)).card : ℝ) = (X.card : ℝ) := by
    have h_nat : (A.card + B.card) + (X \ (A ∪ B)).card = X.card := by
      rw [h_card_diff]
      omega
    exact_mod_cast congr_arg (fun x : ℕ => (x : ℝ)) h_nat
  rw [h_add]

lemma sum_subtype_eq_sum_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (f : ι → ℝ) :
    (∑ i : { i : ι // P i }, f i.1) = ∑ i : ι, if P i then f i else 0 := by
  have h : _ := @Finset.sum_subtype ι ℝ _ P inferInstance (Finset.filter P Finset.univ) (by simp) f
  rw [← h, Finset.sum_filter]

lemma sum_subtype_eq_sum_ite_nat {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (f : ι → ℕ) :
    (∑ i : { i : ι // P i }, f i.1) = ∑ i : ι, if P i then f i else 0 := by
  have h : _ := @Finset.sum_subtype ι ℕ _ P inferInstance (Finset.filter P Finset.univ) (by simp) f
  rw [← h, Finset.sum_filter]

lemma subfamily_card_lt {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ι → Finset α) (x : α) (i0 : ι) (hx : x ∈ A i0 ∪ B i0)
    (h_disj : ∀ i, Disjoint (A i) (B i)) (hA_pos : ∀ i, 1 ≤ (A i).card) :
    (∑ i : { i : ι // x ∉ B i }, ((A i.1 \ {x}).card + (B i.1).card)) < ∑ i : ι, ((A i).card + (B i).card) := by
  have h_ite := sum_subtype_eq_sum_ite_nat (fun i => x ∉ B i) (fun i => (A i \ {x}).card + (B i).card)
  rw [h_ite]
  have h_le : ∀ i ∈ (Finset.univ : Finset ι), (if x ∉ B i then (A i \ {x}).card + (B i).card else 0) ≤ (A i).card + (B i).card := by
    intro i _
    split_ifs with h_notB
    · exact Nat.zero_le _
    · have h_sub : (A i \ {x}).card ≤ (A i).card := Finset.card_le_card (Finset.sdiff_subset : A i \ {x} ⊆ A i)
      exact Nat.add_le_add_right h_sub (B i).card
  have h_lt : (if x ∉ B i0 then (A i0 \ {x}).card + (B i0).card else 0) < (A i0).card + (B i0).card := by
    rw [Finset.mem_union] at hx
    rcases hx with hxA | hxB
    · have hx_notB : x ∉ B i0 := Finset.disjoint_right.mp (h_disj i0).symm hxA
      have h_ite_eq : (if x ∉ B i0 then (A i0 \ {x}).card + (B i0).card else 0) = (A i0 \ {x}).card + (B i0).card := by
        simp [hx_notB]
      rw [h_ite_eq]
      have h_card_eq : (A i0 \ {x}).card = (A i0).card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hxA]
      have hA_pos_i0 : 1 ≤ (A i0).card := hA_pos i0
      omega
    · have hx_not_notB : ¬ (x ∉ B i0) := not_not.mpr hxB
      have h_ite_eq : (if x ∉ B i0 then (A i0 \ {x}).card + (B i0).card else 0) = 0 := by
        simp [hx_not_notB]
      rw [h_ite_eq]
      have hA_pos_i0 : 1 ≤ (A i0).card := hA_pos i0
      omega
  exact Finset.sum_lt_sum h_le ⟨i0, Finset.mem_univ i0, h_lt⟩

lemma bollobas_inductive (n : ℕ) :
    ∀ {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι] [DecidableEq ι]
      (A B : ι → Finset α),
      (∑ i : ι, ((A i).card + (B i).card) = n) →
      (∀ i, Disjoint (A i) (B i)) →
      (∀ i j, i ≠ j → ¬ Disjoint (A i) (B j)) →
      ∑ i : ι, (1 : ℝ) / ((A i).card + (B i).card).choose (A i).card ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro α _ ι _ _ A B hn h_disj h_inter
  by_cases hcard_le1 : Fintype.card ι ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard_le1 with hc0 | hc1
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc0
      simp
    · obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.mp hc1
      rw [Fintype.sum_eq_single i0 (fun j hj => False.elim (hj (hi0 j)))]
      have h_ch_pos : 1 ≤ ((A i0).card + (B i0).card).choose (A i0).card :=
        Nat.choose_pos (by omega)
      have h_ch_r : 1 ≤ (((A i0).card + (B i0).card).choose (A i0).card : ℝ) := by
        exact_mod_cast h_ch_pos
      exact (div_le_one (by linarith)).mpr h_ch_r
  · have hcard_ge2 : 2 ≤ Fintype.card ι := by omega
    have hA_pos : ∀ i : ι, 1 ≤ (A i).card := by
      intro i
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
      have h_not := h_inter i j hj.symm
      have h_ne : (A i ∩ B j).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        exact h_not (Finset.disjoint_iff_inter_eq_empty.mpr he)
      obtain ⟨x, hx⟩ := h_ne
      have hxA : x ∈ A i := (Finset.mem_inter.mp hx).1
      exact Finset.card_pos.mpr ⟨x, hxA⟩
    let X := Finset.biUnion Finset.univ (fun i => A i ∪ B i)
    have hX_pos : 1 ≤ X.card := by
      obtain ⟨i0⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
      have hA0_pos : 0 < (A i0).card := hA_pos i0
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hA0_pos
      have hxX : x ∈ X := Finset.mem_biUnion.mpr ⟨i0, Finset.mem_univ _, Finset.mem_union_left _ hx⟩
      exact Finset.card_pos.mpr ⟨x, hxX⟩
    have hX_r_pos : (0 : ℝ) < (X.card : ℝ) := by
      exact_mod_cast hX_pos
    have h_each_x : ∀ x ∈ X,
        (∑ i : ι, if x ∉ B i then (1 : ℝ) / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ) else 0) ≤ 1 := by
      intro x hx
      let P := fun i : ι => x ∉ B i
      let Ix := { i : ι // P i }
      let A' : Ix → Finset α := fun i => A i.1 \ {x}
      let B' : Ix → Finset α := fun i => B i.1
      have hdisj' : ∀ i : Ix, Disjoint (A' i) (B' i) := by
        intro i
        exact Finset.disjoint_of_subset_left (Finset.sdiff_subset) (h_disj i.1)
      have hinter' : ∀ i j : Ix, i ≠ j → ¬ Disjoint (A' i) (B' j) := by
        intro i j hij
        have hij_ne : i.1 ≠ j.1 := fun heq => hij (Subtype.ext heq)
        have h_not := h_inter i.1 j.1 hij_ne
        have h_ne : (A i.1 ∩ B j.1).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro he
          exact h_not (Finset.disjoint_iff_inter_eq_empty.mpr he)
        obtain ⟨y, hy⟩ := h_ne
        rw [Finset.mem_inter] at hy
        have hy_ne_x : y ≠ x := by
          rintro rfl
          exact j.2 hy.2
        have hyA' : y ∈ A' i := Finset.mem_sdiff.mpr ⟨hy.1, by simp [hy_ne_x]⟩
        have hyB' : y ∈ B' j := hy.2
        intro h_disj_ij
        exact (Finset.disjoint_left.mp h_disj_ij hyA') hyB'
      obtain ⟨i0, _, hxi0⟩ := Finset.mem_biUnion.mp hx
      have hk_lt : (∑ i : Ix, ((A' i).card + (B' i).card)) < n := by
        rw [← hn]
        exact subfamily_card_lt A B x i0 hxi0 h_disj hA_pos
      have h_ih_x := ih (∑ i : Ix, ((A' i).card + (B' i).card)) hk_lt A' B' rfl hdisj' hinter'
      have h_sub_sum := sum_subtype_eq_sum_ite P (fun i => (1 : ℝ) / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ))
      exact h_sub_sum ▸ h_ih_x
    have h_sum_all : (∑ x ∈ X, ∑ i : ι, if x ∉ B i then (1 : ℝ) / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ) else 0) ≤
        ∑ x ∈ X, (1 : ℝ) := Finset.sum_le_sum (fun x hx => h_each_x x hx)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h_sum_all
    rw [Finset.sum_comm] at h_sum_all
    have h_inner : ∀ i : ι,
        (∑ x ∈ X, if x ∉ B i then (1 : ℝ) / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ) else 0) =
          (X.card : ℝ) * (1 / ((A i).card + (B i).card).choose (A i).card : ℝ) := by
      intro i
      have hAi : A i ⊆ X := fun a ha => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_left _ ha⟩
      have hBi : B i ⊆ X := fun b hb => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_union_right _ hb⟩
      have h_single := sum_single_pair_step X (A i) (B i) (h_disj i) hAi hBi (hA_pos i)
      have h_congr : ∀ x ∈ X, (if x ∉ B i then (1 : ℝ) / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ) else 0) =
          (if x ∈ B i then (0 : ℝ) else 1 / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ)) := by
        intro x _
        by_cases hxB : x ∈ B i <;> simp [hxB]
      rw [Finset.sum_congr rfl h_congr]
      exact h_single
    have h_swap : (∑ i : ι, (X.card : ℝ) * (1 / ((A i).card + (B i).card).choose (A i).card : ℝ)) =
        (X.card : ℝ) * ∑ i : ι, (1 / ((A i).card + (B i).card).choose (A i).card : ℝ) := by
      rw [← Finset.mul_sum]
    have h_inner_sum : (∑ i : ι, ∑ x ∈ X, if x ∉ B i then (1 : ℝ) / (((A i \ {x}).card + (B i).card).choose (A i \ {x}).card : ℝ) else 0) =
        (X.card : ℝ) * ∑ i : ι, (1 / ((A i).card + (B i).card).choose (A i).card : ℝ) := by
      rw [Finset.sum_congr rfl (fun i _ => h_inner i), h_swap]
    rw [h_inner_sum] at h_sum_all
    nlinarith

theorem bollobas_two_families {α : Type*} [DecidableEq α] {m : ℕ}
    (A B : Fin m → Finset α)
    (h_disj : ∀ i, Disjoint (A i) (B i))
    (h_inter : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j)) :
    ∑ i : Fin m, (1 : ℝ) / ((A i).card + (B i).card).choose (A i).card ≤ 1 :=
  bollobas_inductive (∑ i : Fin m, ((A i).card + (B i).card)) A B rfl h_disj h_inter

/-- **Uniform Bollobás Two Families Theorem (1965):**
    If $|A_i| = a$ and $|B_i| = b$ for all $i \in \{1, \dots, m\}$, then the number of pairs satisfies
    $m \le \binom{a+b}{a}$. -/
theorem bollobas_uniform {α : Type*} [DecidableEq α] {m a b : ℕ}
    (A B : Fin m → Finset α)
    (h_disj : ∀ i, Disjoint (A i) (B i))
    (h_inter : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j))
    (hA : ∀ i, (A i).card = a)
    (hB : ∀ i, (B i).card = b) :
    (m : ℝ) ≤ (Nat.choose (a + b) a : ℝ) := by
  have h_main := bollobas_two_families A B h_disj h_inter
  have h_const : ∀ i : Fin m, (1 : ℝ) / ((A i).card + (B i).card).choose (A i).card =
      1 / ((a + b).choose a : ℝ) := by
    intro i
    rw [hA i, hB i]
  rw [Finset.sum_congr rfl (fun i _ => h_const i), Finset.sum_const, nsmul_eq_mul] at h_main
  rw [Finset.card_univ, Fintype.card_fin] at h_main
  have h_pos : (0 : ℝ) < ((a + b).choose a : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [mul_one_div] at h_main
  exact (div_le_one₀ h_pos).mp h_main

/-- Integer form of Uniform Bollobás Theorem: $m \le \binom{a+b}{a}$. -/
theorem bollobas_uniform_nat {α : Type*} [DecidableEq α] {m a b : ℕ}
    (A B : Fin m → Finset α)
    (h_disj : ∀ i, Disjoint (A i) (B i))
    (h_inter : ∀ i j, i ≠ j → ¬ Disjoint (A i) (B j))
    (hA : ∀ i, (A i).card = a)
    (hB : ∀ i, (B i).card = b) :
    m ≤ Nat.choose (a + b) a := by
  exact_mod_cast bollobas_uniform A B h_disj h_inter hA hB

