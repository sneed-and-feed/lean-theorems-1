import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Antichain
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace DilworthTheorem

open Finset
open Classical

variable {α : Type*} [DecidableEq α] [PartialOrder α]

/-- A subset of `α` is a chain if every two elements are comparable. -/
def IsChain (s : Set α) : Prop :=
  ∀ x y, x ∈ s → y ∈ s → x ≤ y ∨ y ≤ x

/-- A subset of `α` is an antichain if no two distinct elements are comparable. -/
def IsAntichain (s : Set α) : Prop :=
  ∀ x y, x ∈ s → y ∈ s → x ≠ y → ¬(x ≤ y) ∧ ¬(y ≤ x)

/-- A chain partition / cover of a finset `S` into `k` chains. -/
def IsChainCover (S : Finset α) {k : ℕ} (C : Fin k → Finset α) : Prop :=
  (∀ i, IsChain (C i : Set α)) ∧
  (Finset.biUnion Finset.univ C = S) ∧
  (∀ i j, i ≠ j → Disjoint (C i) (C j))

lemma isChain_empty : IsChain (∅ : Set α) := by
  intro x y hx; exact False.elim hx

lemma isChain_singleton (x : α) : IsChain ({x} : Set α) := by
  intro y z hy hz
  rw [Set.mem_singleton_iff] at hy hz
  subst hy hz
  exact Or.inl le_rfl

lemma isChain_finset_singleton (x : α) : IsChain (({x} : Finset α) : Set α) := by
  rw [coe_singleton]
  exact isChain_singleton x

lemma isChain_subset {s t : Set α} (hst : s ⊆ t) (ht : IsChain t) : IsChain s :=
  fun x y hx hy => ht x y (hst hx) (hst hy)

lemma isAntichain_empty : IsAntichain (∅ : Set α) := by
  intro x y hx; exact False.elim hx

lemma isAntichain_singleton (x : α) : IsAntichain ({x} : Set α) := by
  intro y z hy hz hne
  rw [Set.mem_singleton_iff] at hy hz
  subst hy hz
  exact False.elim (hne rfl)

lemma isAntichain_finset_singleton (x : α) : IsAntichain (({x} : Finset α) : Set α) := by
  rw [coe_singleton]
  exact isAntichain_singleton x

lemma isAntichain_subset {s t : Set α} (hst : s ⊆ t) (ht : IsAntichain t) : IsAntichain s :=
  fun x y hx hy => ht x y (hst hx) (hst hy)

lemma chain_inter_antichain_subsingleton (s t : Set α) (hs : IsChain s) (ht : IsAntichain t) :
    ∀ x y, x ∈ s ∩ t → y ∈ s ∩ t → x = y := by
  intro x y hx hy
  by_contra hne
  have h_comp := hs x y hx.1 hy.1
  have h_incomp := ht x y hx.2 hy.2 hne
  rcases h_comp with hle | hle
  · exact h_incomp.1 hle
  · exact h_incomp.2 hle

lemma chain_inter_antichain_card_le_one (C A : Finset α) (hC : IsChain (C : Set α)) (hA : IsAntichain (A : Set α)) :
    (C ∩ A).card ≤ 1 := by
  rw [card_le_one_iff]
  intro a b ha hb
  simp only [mem_inter] at ha hb
  exact chain_inter_antichain_subsingleton (C : Set α) (A : Set α) hC hA a b
    ⟨ha.1, ha.2⟩ ⟨hb.1, hb.2⟩

lemma chain_has_max (C : Finset α) (hC_nonempty : C.Nonempty) (hC_chain : IsChain (C : Set α)) :
    ∃ m ∈ C, ∀ x ∈ C, x ≤ m := by
  induction' C using Finset.induction_on with a s ha ih
  · exfalso; exact Finset.Nonempty.ne_empty hC_nonempty rfl
  · by_cases hs : s.Nonempty
    · have hs_chain : IsChain (s : Set α) := by
        apply isChain_subset _ hC_chain
        intro x hx; simp [hx]
      rcases ih hs hs_chain with ⟨m, hm, hm_max⟩
      have ham : a ≤ m ∨ m ≤ a := by
        apply hC_chain a m
        · simp
        · simp [hm]
      rcases ham with h | h
      · refine ⟨m, by simp [hm], ?_⟩
        intro x hx
        simp only [mem_insert] at hx
        rcases hx with rfl | hx
        · exact h
        · exact hm_max x hx
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        simp only [mem_insert] at hx
        rcases hx with rfl | hx
        · exact le_rfl
        · exact (hm_max x hx).trans h
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, by simp, by simp⟩

lemma chain_has_min (C : Finset α) (hC_nonempty : C.Nonempty) (hC_chain : IsChain (C : Set α)) :
    ∃ m ∈ C, ∀ x ∈ C, m ≤ x := by
  induction' C using Finset.induction_on with a s ha ih
  · exfalso; exact Finset.Nonempty.ne_empty hC_nonempty rfl
  · by_cases hs : s.Nonempty
    · have hs_chain : IsChain (s : Set α) := by
        apply isChain_subset _ hC_chain
        intro x hx; simp [hx]
      rcases ih hs hs_chain with ⟨m, hm, hm_min⟩
      have ham : a ≤ m ∨ m ≤ a := by
        apply hC_chain a m
        · simp
        · simp [hm]
      rcases ham with h | h
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        simp only [mem_insert] at hx
        rcases hx with rfl | hx
        · exact le_rfl
        · exact h.trans (hm_min x hx)
      · refine ⟨m, by simp [hm], ?_⟩
        intro x hx
        simp only [mem_insert] at hx
        rcases hx with rfl | hx
        · exact h
        · exact hm_min x hx
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      refine ⟨a, by simp, by simp⟩

lemma exists_maximal_chain (S : Finset α) (hS : S.Nonempty) :
    ∃ C : Finset α, C ⊆ S ∧ C.Nonempty ∧ IsChain (C : Set α) ∧
      (∃ cmax ∈ C, ∀ x ∈ S, cmax ≤ x → x = cmax) ∧
      (∃ cmin ∈ C, ∀ x ∈ S, x ≤ cmin → x = cmin) := by
  let F : Finset (Finset α) := S.powerset.filter (fun c => c.Nonempty ∧ IsChain (c : Set α))
  have hF_nonempty : F.Nonempty := by
    rcases hS with ⟨x, hx⟩
    refine ⟨{x}, ?_⟩
    rw [mem_filter, mem_powerset, singleton_subset_iff]
    exact ⟨hx, singleton_nonempty x, isChain_finset_singleton x⟩
  rcases Finset.exists_max_image F Finset.card hF_nonempty with ⟨C, hC_in, hC_max⟩
  rw [mem_filter, mem_powerset] at hC_in
  rcases hC_in with ⟨hC_sub, hC_ne, hC_chain⟩
  refine ⟨C, hC_sub, hC_ne, hC_chain, ?_, ?_⟩
  · rcases chain_has_max C hC_ne hC_chain with ⟨cmax, hcmax_in, hcmax_max⟩
    refine ⟨cmax, hcmax_in, ?_⟩
    intro x0 hx0_in hle
    by_contra hne
    have hlt : cmax < x0 := lt_of_le_of_ne hle (Ne.symm hne)
    have hx_not_in_C : x0 ∉ C := by
      intro hx_C
      have := hcmax_max x0 hx_C
      exact (not_lt_of_ge this) hlt
    let C' := insert x0 C
    have hC'_sub : C' ⊆ S := insert_subset hx0_in hC_sub
    have hC'_ne : C'.Nonempty := insert_nonempty x0 C
    have hC'_chain : IsChain (C' : Set α) := by
      intro u v hu hv
      have hu' : u ∈ C' := hu
      have hv' : v ∈ C' := hv
      rw [mem_insert] at hu' hv'
      rcases hu' with hu_eq | hu_in <;> rcases hv' with hv_eq | hv_in
      · rw [hu_eq, hv_eq]; exact Or.inl le_rfl
      · rw [hu_eq]
        have hv_le := hcmax_max v hv_in
        have hv_lt : v < x0 := hv_le.trans_lt hlt
        exact Or.inr hv_lt.le
      · rw [hv_eq]
        have hu_le := hcmax_max u hu_in
        have hu_lt : u < x0 := hu_le.trans_lt hlt
        exact Or.inl hu_lt.le
      · exact hC_chain u v hu_in hv_in
    have hC'_in_F : C' ∈ F := by
      rw [mem_filter, mem_powerset]
      exact ⟨hC'_sub, hC'_ne, hC'_chain⟩
    have h_card_le := hC_max C' hC'_in_F
    rw [Finset.card_insert_of_notMem hx_not_in_C] at h_card_le
    omega
  · rcases chain_has_min C hC_ne hC_chain with ⟨cmin, hcmin_in, hcmin_min⟩
    refine ⟨cmin, hcmin_in, ?_⟩
    intro x0 hx0_in hle
    by_contra hne
    have hlt : x0 < cmin := lt_of_le_of_ne hle hne
    have hx_not_in_C : x0 ∉ C := by
      intro hx_C
      have := hcmin_min x0 hx_C
      exact (not_lt_of_ge this) hlt
    let C' := insert x0 C
    have hC'_sub : C' ⊆ S := insert_subset hx0_in hC_sub
    have hC'_ne : C'.Nonempty := insert_nonempty x0 C
    have hC'_chain : IsChain (C' : Set α) := by
      intro u v hu hv
      have hu' : u ∈ C' := hu
      have hv' : v ∈ C' := hv
      rw [mem_insert] at hu' hv'
      rcases hu' with hu_eq | hu_in <;> rcases hv' with hv_eq | hv_in
      · rw [hu_eq, hv_eq]; exact Or.inl le_rfl
      · rw [hu_eq]
        have hv_le := hcmin_min v hv_in
        have hx_lt_v : x0 < v := hlt.trans_le hv_le
        exact Or.inl hx_lt_v.le
      · rw [hv_eq]
        have hu_le := hcmin_min u hu_in
        have hx_lt_u : x0 < u := hlt.trans_le hu_le
        exact Or.inr hx_lt_u.le
      · exact hC_chain u v hu_in hv_in
    have hC'_in_F : C' ∈ F := by
      rw [mem_filter, mem_powerset]
      exact ⟨hC'_sub, hC'_ne, hC'_chain⟩
    have h_card_le := hC_max C' hC'_in_F
    rw [Finset.card_insert_of_notMem hx_not_in_C] at h_card_le
    omega

noncomputable def lowerCone (S A : Finset α) : Finset α :=
  S.filter (fun x => ∃ a ∈ A, x ≤ a)

noncomputable def upperCone (S A : Finset α) : Finset α :=
  S.filter (fun x => ∃ a ∈ A, a ≤ x)

lemma lowerCone_subset (S A : Finset α) : lowerCone S A ⊆ S :=
  filter_subset _ S

lemma upperCone_subset (S A : Finset α) : upperCone S A ⊆ S :=
  filter_subset _ S

lemma antichain_subset_lowerCone {S A : Finset α} (hAS : A ⊆ S) : A ⊆ lowerCone S A := by
  intro x hx
  rw [lowerCone, mem_filter]
  exact ⟨hAS hx, x, hx, le_rfl⟩

lemma antichain_subset_upperCone {S A : Finset α} (hAS : A ⊆ S) : A ⊆ upperCone S A := by
  intro x hx
  rw [upperCone, mem_filter]
  exact ⟨hAS hx, x, hx, le_rfl⟩

lemma lowerCone_inter_upperCone {S A : Finset α} (hA_anti : IsAntichain (A : Set α)) (hAS : A ⊆ S) :
    lowerCone S A ∩ upperCone S A = A := by
  ext x
  simp only [mem_inter, lowerCone, upperCone, mem_filter]
  constructor
  · rintro ⟨⟨hxS, a1, ha1, hx_le_a1⟩, ⟨-, a2, ha2, ha2_le_x⟩⟩
    have ha2_le_a1 : a2 ≤ a1 := ha2_le_x.trans hx_le_a1
    have ha1_eq_ha2 : a2 = a1 := by
      by_contra hne
      have := hA_anti a2 a1 (Finset.mem_coe.mpr ha2) (Finset.mem_coe.mpr ha1) hne
      exact this.1 ha2_le_a1
    subst ha1_eq_ha2
    have hx_eq_a2 : x = a2 := le_antisymm hx_le_a1 ha2_le_x
    subst hx_eq_a2
    exact ha2
  · intro hx
    exact ⟨⟨hAS hx, x, hx, le_rfl⟩, ⟨hAS hx, x, hx, le_rfl⟩⟩

lemma lowerCone_union_upperCone (S A : Finset α) (k : ℕ)
    (hAS : A ⊆ S) (hA_anti : IsAntichain (A : Set α)) (hA_card : A.card = k)
    (h_bound : ∀ B ⊆ S, IsAntichain (B : Set α) → B.card ≤ k) :
    lowerCone S A ∪ upperCone S A = S := by
  ext x
  simp only [mem_union, lowerCone, upperCone, mem_filter]
  constructor
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
  · intro hx
    by_contra h_not_in
    have h_not_in_cases : ¬(∃ a ∈ A, x ≤ a) ∧ ¬(∃ a ∈ A, a ≤ x) := by
      constructor
      · intro ⟨a, ha, hle⟩; exact h_not_in (Or.inl ⟨hx, a, ha, hle⟩)
      · intro ⟨a, ha, hle⟩; exact h_not_in (Or.inr ⟨hx, a, ha, hle⟩)
    have hx_not_le : ∀ a ∈ A, ¬(x ≤ a) := fun a ha hle => h_not_in_cases.1 ⟨a, ha, hle⟩
    have hx_ge_not : ∀ a ∈ A, ¬(a ≤ x) := fun a ha hle => h_not_in_cases.2 ⟨a, ha, hle⟩
    have hx_not_in_A : x ∉ A := by
      intro hxA
      exact hx_not_le x hxA le_rfl
    let B := insert x A
    have hB_sub : B ⊆ S := insert_subset hx hAS
    have hB_anti : IsAntichain (B : Set α) := by
      intro u v hu hv hne
      have hu' : u ∈ B := hu
      have hv' : v ∈ B := hv
      rw [mem_insert] at hu' hv'
      rcases hu' with hu_eq | hu_in <;> rcases hv' with hv_eq | hv_in
      · rw [hu_eq, hv_eq] at hne; exact False.elim (hne rfl)
      · rw [hu_eq]
        exact ⟨hx_not_le v hv_in, hx_ge_not v hv_in⟩
      · rw [hv_eq]
        have := (hx_not_le u hu_in)
        have := (hx_ge_not u hu_in)
        exact ⟨‹¬(u ≤ x)›, ‹¬(x ≤ u)›⟩
      · exact hA_anti u v hu_in hv_in hne
    have hB_card : B.card ≤ k := h_bound B hB_sub hB_anti
    rw [Finset.card_insert_of_notMem hx_not_in_A, hA_card] at hB_card
    omega

lemma cmax_not_mem_lowerCone {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hcmax_in : cmax ∈ C) (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    cmax ∉ lowerCone S A := by
  intro h_in
  rw [lowerCone, mem_filter] at h_in
  rcases h_in with ⟨hcmax_S, a, ha_in, hle⟩
  have ha_eq := hcmax_max a (hAS ha_in) hle
  exact (disjoint_left.mp hAC_disj ha_in) (ha_eq ▸ hcmax_in)

lemma cmin_not_mem_upperCone {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hcmin_in : cmin ∈ C) (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    cmin ∉ upperCone S A := by
  intro h_in
  rw [upperCone, mem_filter] at h_in
  rcases h_in with ⟨hcmin_S, a, ha_in, hle⟩
  have ha_eq := hcmin_min a (hAS ha_in) hle
  exact (disjoint_left.mp hAC_disj ha_in) (ha_eq ▸ hcmin_in)

lemma lowerCone_card_lt {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmax_in : cmax ∈ C)
    (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    (lowerCone S A).card < S.card := by
  have h_sub : lowerCone S A ⊆ S := lowerCone_subset S A
  have h_not : cmax ∉ lowerCone S A := cmax_not_mem_lowerCone hAS hcmax_in hcmax_max hAC_disj
  have hcmax_S : cmax ∈ S := hCS hcmax_in
  have : lowerCone S A ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun h_eq => by
    rw [← h_eq] at hcmax_S
    exact h_not hcmax_S⟩
  exact card_lt_card this

lemma upperCone_card_lt {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmin_in : cmin ∈ C)
    (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    (upperCone S A).card < S.card := by
  have h_sub : upperCone S A ⊆ S := upperCone_subset S A
  have h_not : cmin ∉ upperCone S A := cmin_not_mem_upperCone hAS hcmin_in hcmin_min hAC_disj
  have hcmin_S : cmin ∈ S := hCS hcmin_in
  have : upperCone S A ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨h_sub, fun h_eq => by
    rw [← h_eq] at hcmin_S
    exact h_not hcmin_S⟩
  exact card_lt_card this

lemma align_chain_cover {k : ℕ} {T A : Finset α} (hAT : A ⊆ T) (hA_anti : IsAntichain (A : Set α))
    (e : Fin k → α) (he_inj : Function.Injective e) (he_mem : ∀ i, e i ∈ A)
    {C : Fin k → Finset α} (hC : IsChainCover T C) :
    ∃ D : Fin k → Finset α, IsChainCover T D ∧ (∀ i, e i ∈ D i) := by
  have h_exists_j : ∀ i : Fin k, ∃ j : Fin k, e i ∈ C j := by
    intro i
    have he_in_T : e i ∈ T := hAT (he_mem i)
    rw [← hC.2.1, mem_biUnion] at he_in_T
    rcases he_in_T with ⟨j, -, hj⟩
    exact ⟨j, hj⟩
  let tau : Fin k → Fin k := fun i => (h_exists_j i).choose
  have htau_mem : ∀ i, e i ∈ C (tau i) := fun i => (h_exists_j i).choose_spec
  have htau_inj : Function.Injective tau := by
    intro i1 i2 htau_eq
    have he1 : e i1 ∈ (C (tau i1) : Set α) ∩ (A : Set α) := by
      simp only [Set.mem_inter_iff, mem_coe]
      exact ⟨htau_mem i1, he_mem i1⟩
    have he2 : e i2 ∈ (C (tau i1) : Set α) ∩ (A : Set α) := by
      rw [htau_eq]
      simp only [Set.mem_inter_iff, mem_coe]
      exact ⟨htau_mem i2, he_mem i2⟩
    have h_subsingle := chain_inter_antichain_subsingleton (C (tau i1) : Set α) (A : Set α) (hC.1 (tau i1)) hA_anti
    have he_eq := h_subsingle (e i1) (e i2) he1 he2
    exact he_inj he_eq
  have htau_bi : Function.Bijective tau := (Fintype.bijective_iff_injective_and_card tau).mpr ⟨htau_inj, rfl⟩
  let D : Fin k → Finset α := C ∘ tau
  refine ⟨D, ⟨?_, ?_, ?_⟩, htau_mem⟩
  · intro i; exact hC.1 (tau i)
  · rw [← hC.2.1]
    ext x
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨tau i, hi⟩
    · rintro ⟨j, hj⟩
      rcases htau_bi.2 j with ⟨i, rfl⟩
      exact ⟨i, hj⟩
  · intro i j hij
    have : tau i ≠ tau j := fun h => hij (htau_inj h)
    exact hC.2.2 (tau i) (tau j) this

lemma glue_chain_covers {k : ℕ} {S A : Finset α}
    (hA_anti : IsAntichain (A : Set α)) (_hAS : A ⊆ S)
    (h_union : lowerCone S A ∪ upperCone S A = S)
    (h_inter : lowerCone S A ∩ upperCone S A = A)
    (e : Fin k → α) (he_mem : ∀ i, e i ∈ A)
    (D_neg : Fin k → Finset α) (hD_neg : IsChainCover (lowerCone S A) D_neg) (h_mem_neg : ∀ i, e i ∈ D_neg i)
    (D_pos : Fin k → Finset α) (hD_pos : IsChainCover (upperCone S A) D_pos) (h_mem_pos : ∀ i, e i ∈ D_pos i) :
    ∃ C : Fin k → Finset α, IsChainCover S C := by
  let C : Fin k → Finset α := fun i => D_neg i ∪ D_pos i
  have hD_neg_sub : ∀ i, D_neg i ⊆ lowerCone S A := by
    intro i x hx
    rw [← hD_neg.2.1, mem_biUnion]
    exact ⟨i, mem_univ i, hx⟩
  have hD_pos_sub : ∀ i, D_pos i ⊆ upperCone S A := by
    intro i x hx
    rw [← hD_pos.2.1, mem_biUnion]
    exact ⟨i, mem_univ i, hx⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i u v hu hv
    rw [coe_union, Set.mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hD_neg.1 i u v hu hv
    · have hu_cone := hD_neg_sub i hu
      rw [lowerCone, mem_filter] at hu_cone
      rcases hu_cone.2 with ⟨a_u, ha_u_in, hu_le_au⟩
      have hv_cone := hD_pos_sub i hv
      rw [upperCone, mem_filter] at hv_cone
      rcases hv_cone.2 with ⟨a_v, ha_v_in, hav_le_v⟩
      have hu_ei_comp := hD_neg.1 i u (e i) hu (h_mem_neg i)
      have hu_le_ei : u ≤ e i := by
        rcases hu_ei_comp with hle | hle
        · exact hle
        · have hei_le_au : e i ≤ a_u := hle.trans hu_le_au
          have hei_eq_au : e i = a_u := by
            by_contra hne
            have := hA_anti (e i) a_u (he_mem i) ha_u_in hne
            exact this.1 hei_le_au
          have hu_eq_ei : u = e i := le_antisymm (hei_eq_au ▸ hu_le_au) hle
          rw [hu_eq_ei]
      have hv_ei_comp := hD_pos.1 i (e i) v (h_mem_pos i) hv
      have hei_le_v : e i ≤ v := by
        rcases hv_ei_comp with hle | hle
        · exact hle
        · have hav_le_ei : a_v ≤ e i := hav_le_v.trans hle
          have hav_eq_ei : a_v = e i := by
            by_contra hne
            have := hA_anti a_v (e i) ha_v_in (he_mem i) hne
            exact this.1 hav_le_ei
          have hv_eq_ei : v = e i := le_antisymm hle (hav_eq_ei ▸ hav_le_v)
          rw [hv_eq_ei]
      exact Or.inl (hu_le_ei.trans hei_le_v)
    · have hu_cone := hD_pos_sub i hu
      rw [upperCone, mem_filter] at hu_cone
      rcases hu_cone.2 with ⟨a_u, ha_u_in, hau_le_u⟩
      have hv_cone := hD_neg_sub i hv
      rw [lowerCone, mem_filter] at hv_cone
      rcases hv_cone.2 with ⟨a_v, ha_v_in, hv_le_av⟩
      have hu_ei_comp := hD_pos.1 i (e i) u (h_mem_pos i) hu
      have hei_le_u : e i ≤ u := by
        rcases hu_ei_comp with hle | hle
        · exact hle
        · have hau_le_ei : a_u ≤ e i := hau_le_u.trans hle
          have hau_eq_ei : a_u = e i := by
            by_contra hne
            have := hA_anti a_u (e i) ha_u_in (he_mem i) hne
            exact this.1 hau_le_ei
          have hu_eq_ei : u = e i := le_antisymm hle (hau_eq_ei ▸ hau_le_u)
          rw [hu_eq_ei]
      have hv_ei_comp := hD_neg.1 i v (e i) hv (h_mem_neg i)
      have hv_le_ei : v ≤ e i := by
        rcases hv_ei_comp with hle | hle
        · exact hle
        · have hei_le_av : e i ≤ a_v := hle.trans hv_le_av
          have hei_eq_av : e i = a_v := by
            by_contra hne
            have := hA_anti (e i) a_v (he_mem i) ha_v_in hne
            exact this.1 hei_le_av
          have hv_eq_ei : v = e i := le_antisymm (hei_eq_av ▸ hv_le_av) hle
          rw [hv_eq_ei]
      exact Or.inr (hv_le_ei.trans hei_le_u)
    · exact hD_pos.1 i u v hu hv
  · ext x
    simp only [mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨i, hx⟩
      rw [mem_union] at hx
      rcases hx with hx | hx
      · have : x ∈ lowerCone S A := hD_neg_sub i hx
        rw [← h_union, mem_union]
        exact Or.inl this
      · have : x ∈ upperCone S A := hD_pos_sub i hx
        rw [← h_union, mem_union]
        exact Or.inr this
    · intro hx
      rw [← h_union, mem_union] at hx
      rcases hx with hx | hx
      · rw [← hD_neg.2.1, mem_biUnion] at hx
        rcases hx with ⟨i, -, hi⟩
        refine ⟨i, ?_⟩
        rw [mem_union]
        exact Or.inl hi
      · rw [← hD_pos.2.1, mem_biUnion] at hx
        rcases hx with ⟨i, -, hi⟩
        refine ⟨i, ?_⟩
        rw [mem_union]
        exact Or.inr hi
  · intro i j hij
    rw [disjoint_iff_ne]
    rintro u hu v hv rfl
    have hu_un : u ∈ D_neg i ∪ D_pos i := hu
    have hv_un : u ∈ D_neg j ∪ D_pos j := hv
    rw [mem_union] at hu_un hv_un
    have h_in_S : u ∈ S := by
      rcases hu_un with hu_in | hu_in
      · exact (lowerCone_subset S A) (hD_neg_sub i hu_in)
      · exact (upperCone_subset S A) (hD_pos_sub i hu_in)
    rw [← h_union, mem_union] at h_in_S
    rcases h_in_S with hu_neg | hu_pos
    · have hu_in_Dneg_i : u ∈ D_neg i := by
        rcases hu_un with hu_in | hu_in
        · exact hu_in
        · have hu_in_pos : u ∈ upperCone S A := hD_pos_sub i hu_in
          have hu_in_A : u ∈ A := by
            rw [← h_inter, mem_inter]
            exact ⟨hu_neg, hu_in_pos⟩
          have : u ∈ (D_pos i : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨hu_in, hu_in_A⟩
          have hei_in : e i ∈ (D_pos i : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨h_mem_pos i, he_mem i⟩
          have hu_eq_ei := chain_inter_antichain_subsingleton (D_pos i) A (hD_pos.1 i) hA_anti u (e i) this hei_in
          subst hu_eq_ei
          exact h_mem_neg i
      have hu_in_Dneg_j : u ∈ D_neg j := by
        rcases hv_un with hv_in | hv_in
        · exact hv_in
        · have hu_in_pos : u ∈ upperCone S A := hD_pos_sub j hv_in
          have hu_in_A : u ∈ A := by
            rw [← h_inter, mem_inter]
            exact ⟨hu_neg, hu_in_pos⟩
          have : u ∈ (D_pos j : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨hv_in, hu_in_A⟩
          have hej_in : e j ∈ (D_pos j : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨h_mem_pos j, he_mem j⟩
          have hu_eq_ej := chain_inter_antichain_subsingleton (D_pos j) A (hD_pos.1 j) hA_anti u (e j) this hej_in
          subst hu_eq_ej
          exact h_mem_neg j
      exact (disjoint_left.mp (hD_neg.2.2 i j hij) hu_in_Dneg_i) hu_in_Dneg_j
    · have hu_in_Dpos_i : u ∈ D_pos i := by
        rcases hu_un with hu_in | hu_in
        · have hu_in_neg : u ∈ lowerCone S A := hD_neg_sub i hu_in
          have hu_in_A : u ∈ A := by
            rw [← h_inter, mem_inter]
            exact ⟨hu_in_neg, hu_pos⟩
          have : u ∈ (D_neg i : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨hu_in, hu_in_A⟩
          have hei_in : e i ∈ (D_neg i : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨h_mem_neg i, he_mem i⟩
          have hu_eq_ei := chain_inter_antichain_subsingleton (D_neg i) A (hD_neg.1 i) hA_anti u (e i) this hei_in
          subst hu_eq_ei
          exact h_mem_pos i
        · exact hu_in
      have hu_in_Dpos_j : u ∈ D_pos j := by
        rcases hv_un with hv_in | hv_in
        · have hu_in_neg : u ∈ lowerCone S A := hD_neg_sub j hv_in
          have hu_in_A : u ∈ A := by
            rw [← h_inter, mem_inter]
            exact ⟨hu_in_neg, hu_pos⟩
          have : u ∈ (D_neg j : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨hv_in, hu_in_A⟩
          have hej_in : e j ∈ (D_neg j : Set α) ∩ (A : Set α) := by
            simp only [Set.mem_inter_iff, mem_coe]
            exact ⟨h_mem_neg j, he_mem j⟩
          have hu_eq_ej := chain_inter_antichain_subsingleton (D_neg j) A (hD_neg.1 j) hA_anti u (e j) this hej_in
          subst hu_eq_ej
          exact h_mem_pos j
        · exact hv_in
      exact (disjoint_left.mp (hD_pos.2.2 i j hij) hu_in_Dpos_i) hu_in_Dpos_j

lemma extend_chain_cover {m : ℕ} {S C : Finset α}
    (hCS : C ⊆ S) (hC_chain : IsChain (C : Set α))
    (C_prev : Fin m → Finset α) (hC_prev : IsChainCover (S \ C) C_prev) :
    ∃ D : Fin (m + 1) → Finset α, IsChainCover S D := by
  refine ⟨Fin.cons C C_prev, ?_, ?_, ?_⟩
  · intro i
    induction' i using Fin.cases with j
    · rw [Fin.cons_zero]; exact hC_chain
    · rw [Fin.cons_succ]; exact hC_prev.1 j
  · have h_biUnion : Finset.biUnion Finset.univ (Fin.cons C C_prev) = C ∪ (Finset.biUnion Finset.univ C_prev) := by
      ext x
      simp only [mem_biUnion, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        induction' i using Fin.cases with j
        · rw [Fin.cons_zero] at hi; exact Or.inl hi
        · rw [Fin.cons_succ] at hi; exact Or.inr ⟨j, hi⟩
      · rintro (hx_in_C | ⟨j, hj⟩)
        · refine ⟨0, ?_⟩
          rwa [Fin.cons_zero]
        · refine ⟨j.succ, ?_⟩
          rwa [Fin.cons_succ]
    rw [h_biUnion, hC_prev.2.1, union_comm, sdiff_union_of_subset hCS]
  · intro i j hij
    induction' i using Fin.cases with i'
    · induction' j using Fin.cases with j'
      · exact False.elim (hij rfl)
      · rw [Fin.cons_zero, Fin.cons_succ]
        have h_sub : C_prev j' ⊆ S \ C := by
          intro x hx
          rw [← hC_prev.2.1, mem_biUnion]
          exact ⟨j', mem_univ j', hx⟩
        rw [disjoint_iff_ne]
        rintro u hu v hv rfl
        have hv_sdiff : u ∈ S \ C := h_sub hv
        rw [mem_sdiff] at hv_sdiff
        exact hv_sdiff.2 hu
    · induction' j using Fin.cases with j'
      · rw [Fin.cons_succ, Fin.cons_zero]
        have h_sub : C_prev i' ⊆ S \ C := by
          intro x hx
          rw [← hC_prev.2.1, mem_biUnion]
          exact ⟨i', mem_univ i', hx⟩
        rw [disjoint_iff_ne]
        rintro u hu v hv rfl
        have hu_sdiff : u ∈ S \ C := h_sub hu
        rw [mem_sdiff] at hu_sdiff
        exact hu_sdiff.2 hv
      · rw [Fin.cons_succ, Fin.cons_succ]
        have : i' ≠ j' := fun h => hij (congr_arg Fin.succ h)
        exact hC_prev.2.2 i' j' this

/-- **Dilworth's Theorem (R. P. Dilworth, 1950):**
If every antichain in a finite poset `S` has size at most `k`, then `S` can be partitioned
into `k` chains. -/
theorem dilworth_theorem (S : Finset α) (k : ℕ)
    (h_anti : ∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) :
    ∃ C : Fin k → Finset α, IsChainCover S C := by
  have h_main : ∀ n, ∀ (S : Finset α) (k : ℕ), S.card = n →
      (∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) →
      ∃ C : Fin k → Finset α, IsChainCover S C := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    intro S k hn h_anti
    by_cases hn0 : n = 0
    · subst hn0
      rw [Finset.card_eq_zero] at hn
      subst hn
      refine ⟨fun (_ : Fin k) => (∅ : Finset α), ?_, ?_, ?_⟩
      · intro i
        have : ((fun _ : Fin k => (∅ : Finset α)) i : Set α) = ∅ := by simp
        rw [this]
        exact isChain_empty
      · ext x; simp
      · intro i j hij; exact disjoint_empty_left _
    · by_cases hk0 : k = 0
      · subst hk0
        have hS_ne : S.Nonempty := card_pos.mp (by omega)
        rcases hS_ne with ⟨x, hx⟩
        have h_sing : IsAntichain (({x} : Finset α) : Set α) := isAntichain_finset_singleton x
        have h_card := h_anti {x} (singleton_subset_iff.mpr hx) h_sing
        simp at h_card
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk0
        have hS_ne : S.Nonempty := card_pos.mp (by omega)
        rcases exists_maximal_chain S hS_ne with ⟨C, hCS, hC_ne, hC_chain, ⟨cmax, hcmax_in, hcmax_max⟩, ⟨cmin, hcmin_in, hcmin_min⟩⟩
        by_cases h_case1 : ∀ A ⊆ S \ C, IsAntichain (A : Set α) → A.card ≤ m
        · have h_card_lt : (S \ C).card < n := by
            rw [← hn, card_sdiff_of_subset hCS]
            have : 0 < C.card := card_pos.mpr hC_ne
            omega
          rcases ih (S \ C).card h_card_lt (S \ C) m rfl h_case1 with ⟨C_prev, hC_prev⟩
          exact extend_chain_cover hCS hC_chain C_prev hC_prev
        · have h_exists : ∃ A ⊆ S \ C, IsAntichain (A : Set α) ∧ m < A.card := by
            by_contra! h_all
            exact h_case1 h_all
          rcases h_exists with ⟨A, hA_sub, hA_anti, hA_card_gt⟩
          have hAS : A ⊆ S := hA_sub.trans sdiff_subset
          have hA_card_le := h_anti A hAS hA_anti
          have hA_card : A.card = m + 1 := by omega
          have hAC_disj : Disjoint A C := disjoint_left.mpr (fun a ha haC => (mem_sdiff.mp (hA_sub ha)).2 haC)
          have h_union := lowerCone_union_upperCone S A (m + 1) hAS hA_anti hA_card h_anti
          have h_inter := lowerCone_inter_upperCone hA_anti hAS
          have h_neg_lt : (lowerCone S A).card < n := by
            rw [← hn]
            exact lowerCone_card_lt hAS hCS hcmax_in hcmax_max hAC_disj
          have h_pos_lt : (upperCone S A).card < n := by
            rw [← hn]
            exact upperCone_card_lt hAS hCS hcmin_in hcmin_min hAC_disj
          have h_anti_neg : ∀ B ⊆ lowerCone S A, IsAntichain (B : Set α) → B.card ≤ m + 1 := by
            intro B hB
            exact h_anti B (hB.trans (lowerCone_subset S A))
          have h_anti_pos : ∀ B ⊆ upperCone S A, IsAntichain (B : Set α) → B.card ≤ m + 1 := by
            intro B hB
            exact h_anti B (hB.trans (upperCone_subset S A))
          rcases ih (lowerCone S A).card h_neg_lt (lowerCone S A) (m + 1) rfl h_anti_neg with ⟨C_neg, hC_neg⟩
          rcases ih (upperCone S A).card h_pos_lt (upperCone S A) (m + 1) rfl h_anti_pos with ⟨C_pos, hC_pos⟩
          let e_equiv : Fin (m + 1) ≃ {x // x ∈ A} :=
            (Fin.castOrderIso (hA_card.symm)).toEquiv.trans (Finset.equivFin A).symm
          let e : Fin (m + 1) → α := fun i => (e_equiv i).1
          have he_inj : Function.Injective e := fun i1 i2 h => e_equiv.injective (Subtype.ext h)
          have he_mem : ∀ i, e i ∈ A := fun i => (e_equiv i).2
          have hA_neg : A ⊆ lowerCone S A := antichain_subset_lowerCone hAS
          have hA_pos : A ⊆ upperCone S A := antichain_subset_upperCone hAS
          rcases align_chain_cover hA_neg hA_anti e he_inj he_mem hC_neg with ⟨D_neg, hD_neg, h_mem_neg⟩
          rcases align_chain_cover hA_pos hA_anti e he_inj he_mem hC_pos with ⟨D_pos, hD_pos, h_mem_pos⟩
          exact glue_chain_covers hA_anti hAS h_union h_inter e he_mem D_neg hD_neg h_mem_neg D_pos hD_pos h_mem_pos
  exact h_main S.card S k rfl h_anti

/-- **Dilworth's Min-Max Equivalence:**
The maximum size of an antichain equals the minimum number of chains covering the poset. -/
theorem dilworth_duality [Fintype α] (w : ℕ)
    (h_max : ∃ A : Finset α, IsAntichain (A : Set α) ∧ A.card = w)
    (h_bound : ∀ A : Finset α, IsAntichain (A : Set α) → A.card ≤ w) :
    (∃ C : Fin w → Finset α, IsChainCover Finset.univ C) ∧
    (∀ k < w, ¬ ∃ C : Fin k → Finset α, IsChainCover Finset.univ C) := by
  constructor
  · apply dilworth_theorem Finset.univ w
    intro A _ hA
    exact h_bound A hA
  · intro k hk ⟨C, hC⟩
    rcases h_max with ⟨A, hA_anti, hA_card⟩
    have h_cov : A ⊆ Finset.biUnion Finset.univ (fun i => A ∩ C i) := by
      intro x hx
      have hx_univ : x ∈ (Finset.univ : Finset α) := mem_univ x
      rw [← hC.2.1, mem_biUnion] at hx_univ
      rcases hx_univ with ⟨i, -, hi⟩
      rw [mem_biUnion]
      exact ⟨i, mem_univ i, mem_inter.mpr ⟨hx, hi⟩⟩
    have h_card_le := card_le_card h_cov
    have h_sum := h_card_le.trans (card_biUnion_le)
    have h_term_le : ∀ i ∈ (Finset.univ : Finset (Fin k)), (A ∩ C i).card ≤ 1 := by
      intro i _
      rw [inter_comm]
      exact chain_inter_antichain_card_le_one (C i) A (hC.1 i) hA_anti
    have h_sum_le : (Finset.univ : Finset (Fin k)).sum (fun i => (A ∩ C i).card) ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 1) :=
      sum_le_sum h_term_le
    rw [sum_const, nsmul_eq_mul, mul_one, card_univ, Fintype.card_fin] at h_sum_le
    rw [hA_card] at h_sum
    have : w ≤ k := h_sum.trans h_sum_le
    omega

#print axioms dilworth_theorem
#print axioms dilworth_duality

end DilworthTheorem
