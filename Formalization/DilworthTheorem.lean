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

/-- An antichain partition / cover of a finset `S` into `k` antichains. -/
def IsAntichainCover (S : Finset α) {k : ℕ} (A : Fin k → Finset α) : Prop :=
  (∀ i, IsAntichain (A i : Set α)) ∧
  (Finset.biUnion Finset.univ A = S) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j))

lemma isChain_empty : IsChain (∅ : Set α) := fun _ _ h => h.elim

lemma isChain_singleton (x : α) : IsChain ({x} : Set α) := by
  rintro y z rfl rfl; exact Or.inl le_rfl

lemma isChain_finset_singleton (x : α) : IsChain (({x} : Finset α) : Set α) := by
  rw [coe_singleton]; exact isChain_singleton x

lemma isChain_subset {s t : Set α} (hst : s ⊆ t) (ht : IsChain t) : IsChain s :=
  fun x y hx hy => ht x y (hst hx) (hst hy)

lemma isAntichain_empty : IsAntichain (∅ : Set α) := fun _ _ h => h.elim

lemma isAntichain_singleton (x : α) : IsAntichain ({x} : Set α) := by
  rintro y z rfl rfl hne; exact (hne rfl).elim

lemma isAntichain_finset_singleton (x : α) : IsAntichain (({x} : Finset α) : Set α) := by
  rw [coe_singleton]; exact isAntichain_singleton x

lemma isAntichain_subset {s t : Set α} (hst : s ⊆ t) (ht : IsAntichain t) : IsAntichain s :=
  fun x y hx hy => ht x y (hst hx) (hst hy)

lemma chain_inter_antichain_subsingleton (s t : Set α) (hs : IsChain s) (ht : IsAntichain t) :
    ∀ x y, x ∈ s ∩ t → y ∈ s ∩ t → x = y := by
  intro x y ⟨hxs, hxt⟩ ⟨hys, hyt⟩; by_contra hne
  rcases hs x y hxs hys with h | h <;> [exact (ht x y hxt hyt hne).1 h; exact (ht x y hxt hyt hne).2 h]

lemma chain_inter_antichain_card_le_one (C A : Finset α) (hC : IsChain (C : Set α)) (hA : IsAntichain (A : Set α)) :
    (C ∩ A).card ≤ 1 := by
  rw [card_le_one_iff]; intro a b ha hb
  exact chain_inter_antichain_subsingleton (C : Set α) (A : Set α) hC hA a b (mem_inter.mp ha) (mem_inter.mp hb)

lemma chain_has_max (C : Finset α) (hC_nonempty : C.Nonempty) (hC_chain : IsChain (C : Set α)) :
    ∃ m ∈ C, ∀ x ∈ C, x ≤ m := by
  induction' C using Finset.induction_on with a s ha ih
  · cases hC_nonempty.ne_empty rfl
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, mem_singleton_self a, by simp⟩
    · rcases ih hs (isChain_subset (subset_insert a s) hC_chain) with ⟨m, hm, hm_max⟩
      rcases hC_chain a m (mem_insert_self a s) (mem_insert_of_mem hm) with h | h
      · exact ⟨m, mem_insert_of_mem hm, fun x hx => (mem_insert.mp hx).elim (fun e => e ▸ h) (hm_max x)⟩
      · exact ⟨a, mem_insert_self a s, fun x hx => (mem_insert.mp hx).elim (fun e => e ▸ le_rfl) (fun hx => (hm_max x hx).trans h)⟩

lemma chain_has_min (C : Finset α) (hC_nonempty : C.Nonempty) (hC_chain : IsChain (C : Set α)) :
    ∃ m ∈ C, ∀ x ∈ C, m ≤ x := by
  induction' C using Finset.induction_on with a s ha ih
  · cases hC_nonempty.ne_empty rfl
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, mem_singleton_self a, by simp⟩
    · rcases ih hs (isChain_subset (subset_insert a s) hC_chain) with ⟨m, hm, hm_min⟩
      rcases hC_chain a m (mem_insert_self a s) (mem_insert_of_mem hm) with h | h
      · exact ⟨a, mem_insert_self a s, fun x hx => (mem_insert.mp hx).elim (fun e => e ▸ le_rfl) (fun hx => h.trans (hm_min x hx))⟩
      · exact ⟨m, mem_insert_of_mem hm, fun x hx => (mem_insert.mp hx).elim (fun e => e ▸ h) (hm_min x)⟩

lemma exists_maximal_chain (S : Finset α) (hS : S.Nonempty) :
    ∃ C : Finset α, C ⊆ S ∧ C.Nonempty ∧ IsChain (C : Set α) ∧
      (∃ cmax ∈ C, ∀ x ∈ S, cmax ≤ x → x = cmax) ∧
      (∃ cmin ∈ C, ∀ x ∈ S, x ≤ cmin → x = cmin) := by
  rcases hS with ⟨x, hx⟩
  let F : Finset (Finset α) := S.powerset.filter (fun c => c.Nonempty ∧ IsChain (c : Set α))
  have hF_ne : F.Nonempty := ⟨{x}, mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr hx), singleton_nonempty x, isChain_finset_singleton x⟩⟩
  rcases Finset.exists_max_image F Finset.card hF_ne with ⟨C, hC_in, hC_max⟩
  simp only [mem_filter, mem_powerset, F] at hC_in
  rcases hC_in with ⟨hC_sub, hC_ne, hC_chain⟩
  rcases chain_has_max C hC_ne hC_chain with ⟨cmax, hcmax_in, hcmax_max⟩
  rcases chain_has_min C hC_ne hC_chain with ⟨cmin, hcmin_in, hcmin_min⟩
  refine ⟨C, hC_sub, hC_ne, hC_chain, ⟨cmax, hcmax_in, fun x0 hx0 hle => ?_⟩, ⟨cmin, hcmin_in, fun x0 hx0 hle => ?_⟩⟩
  · by_contra hne
    have hlt : cmax < x0 := lt_of_le_of_ne hle (Ne.symm hne)
    have hx_not : x0 ∉ C := fun h => (not_lt_of_ge (hcmax_max x0 h)) hlt
    have hC'_chain : IsChain ((insert x0 C : Finset α) : Set α) := by
      intro u v hu hv; simp only [mem_coe, mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact Or.inl le_rfl
      · exact Or.inr ((hcmax_max v hv).trans_lt hlt).le
      · exact Or.inl ((hcmax_max u hu).trans_lt hlt).le
      · exact hC_chain u v hu hv
    have hC'_in : insert x0 C ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx0 hC_sub), insert_nonempty x0 C, hC'_chain⟩
    have h_le := hC_max (insert x0 C) hC'_in
    rw [card_insert_of_notMem hx_not] at h_le; omega
  · by_contra hne
    have hlt : x0 < cmin := lt_of_le_of_ne hle hne
    have hx_not : x0 ∉ C := fun h => (not_lt_of_ge (hcmin_min x0 h)) hlt
    have hC'_chain : IsChain ((insert x0 C : Finset α) : Set α) := by
      intro u v hu hv; simp only [mem_coe, mem_insert] at hu hv
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact Or.inl le_rfl
      · exact Or.inl (hlt.trans_le (hcmin_min v hv)).le
      · exact Or.inr (hlt.trans_le (hcmin_min u hu)).le
      · exact hC_chain u v hu hv
    have hC'_in : insert x0 C ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx0 hC_sub), insert_nonempty x0 C, hC'_chain⟩
    have h_le := hC_max (insert x0 C) hC'_in
    rw [card_insert_of_notMem hx_not] at h_le; omega

noncomputable def lowerCone (S A : Finset α) : Finset α :=
  S.filter (fun x => ∃ a ∈ A, x ≤ a)

noncomputable def upperCone (S A : Finset α) : Finset α :=
  S.filter (fun x => ∃ a ∈ A, a ≤ x)

lemma lowerCone_subset (S A : Finset α) : lowerCone S A ⊆ S := filter_subset _ S

lemma upperCone_subset (S A : Finset α) : upperCone S A ⊆ S := filter_subset _ S

lemma antichain_subset_lowerCone {S A : Finset α} (hAS : A ⊆ S) : A ⊆ lowerCone S A :=
  fun x hx => mem_filter.mpr ⟨hAS hx, x, hx, le_rfl⟩

lemma antichain_subset_upperCone {S A : Finset α} (hAS : A ⊆ S) : A ⊆ upperCone S A :=
  fun x hx => mem_filter.mpr ⟨hAS hx, x, hx, le_rfl⟩

lemma lowerCone_inter_upperCone {S A : Finset α} (hA_anti : IsAntichain (A : Set α)) (hAS : A ⊆ S) :
    lowerCone S A ∩ upperCone S A = A := by
  ext x; simp only [mem_inter, lowerCone, upperCone, mem_filter]
  refine ⟨?_, fun hx => ⟨⟨hAS hx, x, hx, le_rfl⟩, ⟨hAS hx, x, hx, le_rfl⟩⟩⟩
  rintro ⟨⟨-, a1, ha1, hx1⟩, ⟨-, a2, ha2, hx2⟩⟩
  have heq : a2 = a1 := by by_contra hne; exact (hA_anti a2 a1 ha2 ha1 hne).1 (hx2.trans hx1)
  subst heq; exact le_antisymm hx1 hx2 ▸ ha1

lemma lowerCone_union_upperCone (S A : Finset α) (k : ℕ)
    (hAS : A ⊆ S) (hA_anti : IsAntichain (A : Set α)) (hA_card : A.card = k)
    (h_bound : ∀ B ⊆ S, IsAntichain (B : Set α) → B.card ≤ k) :
    lowerCone S A ∪ upperCone S A = S := by
  ext x; simp only [mem_union, lowerCone, upperCone, mem_filter]
  refine ⟨by rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx, fun hx => ?_⟩
  simp only [hx, true_and]; by_contra! h_not
  have hB_anti : IsAntichain ((insert x A : Finset α) : Set α) := by
    intro u v hu hv hne; simp only [mem_coe, mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact (hne rfl).elim
    · exact ⟨h_not.1 v hv, h_not.2 v hv⟩
    · exact ⟨h_not.2 u hu, h_not.1 u hu⟩
    · exact hA_anti u v hu hv hne
  have hB_card := h_bound (insert x A) (insert_subset hx hAS) hB_anti
  have hx_not : x ∉ A := fun h => h_not.1 x h le_rfl
  rw [card_insert_of_notMem hx_not, hA_card] at hB_card; omega

lemma cmax_not_mem_lowerCone {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hcmax_in : cmax ∈ C) (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    cmax ∉ lowerCone S A := by
  intro h; rw [lowerCone, mem_filter] at h; rcases h with ⟨-, a, ha, hle⟩
  exact (disjoint_left.mp hAC_disj ha) (hcmax_max a (hAS ha) hle ▸ hcmax_in)

lemma cmin_not_mem_upperCone {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hcmin_in : cmin ∈ C) (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    cmin ∉ upperCone S A := by
  intro h; rw [upperCone, mem_filter] at h; rcases h with ⟨-, a, ha, hle⟩
  exact (disjoint_left.mp hAC_disj ha) (hcmin_min a (hAS ha) hle ▸ hcmin_in)

lemma lowerCone_card_lt {S A C : Finset α} {cmax : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmax_in : cmax ∈ C)
    (hcmax_max : ∀ x ∈ S, cmax ≤ x → x = cmax)
    (hAC_disj : Disjoint A C) :
    (lowerCone S A).card < S.card := by
  refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨lowerCone_subset S A, fun h => ?_⟩)
  have hc : cmax ∈ lowerCone S A := by rw [h]; exact hCS hcmax_in
  exact cmax_not_mem_lowerCone hAS hcmax_in hcmax_max hAC_disj hc

lemma upperCone_card_lt {S A C : Finset α} {cmin : α}
    (hAS : A ⊆ S) (hCS : C ⊆ S) (hcmin_in : cmin ∈ C)
    (hcmin_min : ∀ x ∈ S, x ≤ cmin → x = cmin)
    (hAC_disj : Disjoint A C) :
    (upperCone S A).card < S.card := by
  refine card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨upperCone_subset S A, fun h => ?_⟩)
  have hc : cmin ∈ upperCone S A := by rw [h]; exact hCS hcmin_in
  exact cmin_not_mem_upperCone hAS hcmin_in hcmin_min hAC_disj hc

lemma align_chain_cover {k : ℕ} {T A : Finset α} (hAT : A ⊆ T) (hA_anti : IsAntichain (A : Set α))
    (e : Fin k → α) (he_inj : Function.Injective e) (he_mem : ∀ i, e i ∈ A)
    {C : Fin k → Finset α} (hC : IsChainCover T C) :
    ∃ D : Fin k → Finset α, IsChainCover T D ∧ (∀ i, e i ∈ D i) := by
  have h_ex : ∀ i : Fin k, ∃ j : Fin k, e i ∈ C j := by
    intro i; have : e i ∈ Finset.biUnion Finset.univ C := by rw [hC.2.1]; exact hAT (he_mem i)
    simpa [mem_biUnion] using this
  let tau : Fin k → Fin k := fun i => (h_ex i).choose
  have htau_mem : ∀ i, e i ∈ C (tau i) := fun i => (h_ex i).choose_spec
  have htau_inj : Function.Injective tau := by
    intro i1 i2 h
    have heq := chain_inter_antichain_subsingleton (C (tau i1)) A (hC.1 (tau i1)) hA_anti (e i1) (e i2)
      ⟨htau_mem i1, he_mem i1⟩ ⟨h ▸ htau_mem i2, he_mem i2⟩
    exact he_inj heq
  have htau_bi : Function.Bijective tau := (Fintype.bijective_iff_injective_and_card tau).mpr ⟨htau_inj, rfl⟩
  refine ⟨C ∘ tau, ⟨fun i => hC.1 (tau i), ?_, fun i j hij => hC.2.2 (tau i) (tau j) (fun h => hij (htau_inj h))⟩, htau_mem⟩
  rw [← hC.2.1]
  ext x; simp only [mem_biUnion, mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ => ⟨tau i, hi⟩, fun ⟨j, hj⟩ => by rcases htau_bi.2 j with ⟨i, rfl⟩; exact ⟨i, hj⟩⟩

lemma lowerCone_chain_le {D A : Finset α} {e u : α}
    (hD_chain : IsChain (D : Set α)) (hA_anti : IsAntichain (A : Set α))
    (heD : e ∈ D) (heA : e ∈ A) (huD : u ∈ D) (hu_cone : ∃ a ∈ A, u ≤ a) :
    u ≤ e := by
  rcases hD_chain u e huD heD with hle | hle
  · exact hle
  · rcases hu_cone with ⟨a, ha, hu_le_a⟩
    have : e = a := by by_contra hne; exact (hA_anti e a heA ha hne).1 (hle.trans hu_le_a)
    subst this; exact hu_le_a

lemma upperCone_chain_le {D A : Finset α} {e v : α}
    (hD_chain : IsChain (D : Set α)) (hA_anti : IsAntichain (A : Set α))
    (heD : e ∈ D) (heA : e ∈ A) (hvD : v ∈ D) (hv_cone : ∃ a ∈ A, a ≤ v) :
    e ≤ v := by
  rcases hD_chain e v heD hvD with hle | hle
  · exact hle
  · rcases hv_cone with ⟨a, ha, ha_le_v⟩
    have : a = e := by by_contra hne; exact (hA_anti a e ha heA hne).1 (ha_le_v.trans hle)
    subst this; exact ha_le_v

lemma cover_inter_antichain_eq {D A : Finset α} {e u : α}
    (hD_chain : IsChain (D : Set α)) (hA_anti : IsAntichain (A : Set α))
    (heD : e ∈ D) (heA : e ∈ A) (huD : u ∈ D) (huA : u ∈ A) : u = e :=
  chain_inter_antichain_subsingleton D A hD_chain hA_anti u e ⟨huD, huA⟩ ⟨heD, heA⟩

lemma glue_chain_covers {k : ℕ} {S A : Finset α}
    (hA_anti : IsAntichain (A : Set α)) (_hAS : A ⊆ S)
    (h_union : lowerCone S A ∪ upperCone S A = S)
    (h_inter : lowerCone S A ∩ upperCone S A = A)
    (e : Fin k → α) (he_mem : ∀ i, e i ∈ A)
    (D_neg : Fin k → Finset α) (hD_neg : IsChainCover (lowerCone S A) D_neg) (h_mem_neg : ∀ i, e i ∈ D_neg i)
    (D_pos : Fin k → Finset α) (hD_pos : IsChainCover (upperCone S A) D_pos) (h_mem_pos : ∀ i, e i ∈ D_pos i) :
    ∃ C : Fin k → Finset α, IsChainCover S C := by
  let C : Fin k → Finset α := fun i => D_neg i ∪ D_pos i
  have hD_neg_sub : ∀ i, D_neg i ⊆ lowerCone S A := fun i x hx => by rw [← hD_neg.2.1, mem_biUnion]; exact ⟨i, mem_univ i, hx⟩
  have hD_pos_sub : ∀ i, D_pos i ⊆ upperCone S A := fun i x hx => by rw [← hD_pos.2.1, mem_biUnion]; exact ⟨i, mem_univ i, hx⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i u v hu hv
    simp only [mem_coe, mem_union, C] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hD_neg.1 i u v hu hv
    · have hu_le := lowerCone_chain_le (hD_neg.1 i) hA_anti (h_mem_neg i) (he_mem i) hu (mem_filter.mp (hD_neg_sub i hu)).2
      have hv_ge := upperCone_chain_le (hD_pos.1 i) hA_anti (h_mem_pos i) (he_mem i) hv (mem_filter.mp (hD_pos_sub i hv)).2
      exact Or.inl (hu_le.trans hv_ge)
    · have hu_ge := upperCone_chain_le (hD_pos.1 i) hA_anti (h_mem_pos i) (he_mem i) hu (mem_filter.mp (hD_pos_sub i hu)).2
      have hv_le := lowerCone_chain_le (hD_neg.1 i) hA_anti (h_mem_neg i) (he_mem i) hv (mem_filter.mp (hD_neg_sub i hv)).2
      exact Or.inr (hv_le.trans hu_ge)
    · exact hD_pos.1 i u v hu hv
  · rw [← h_union, ← hD_neg.2.1, ← hD_pos.2.1]
    ext x; simp only [mem_biUnion, mem_univ, true_and, mem_union, C]
    exact ⟨fun ⟨i, hi⟩ => hi.elim (fun h => Or.inl ⟨i, h⟩) (fun h => Or.inr ⟨i, h⟩),
           fun h => h.elim (fun ⟨i, h⟩ => ⟨i, Or.inl h⟩) (fun ⟨i, h⟩ => ⟨i, Or.inr h⟩)⟩
  · intro i j hij
    rw [disjoint_iff_ne]; rintro u hu _ hv rfl
    have hu_sub : ∀ k, u ∈ D_neg k ∪ D_pos k → (u ∈ lowerCone S A → u ∈ D_neg k) ∧ (u ∈ upperCone S A → u ∈ D_pos k) := by
      intro k hk; rcases mem_union.mp hk with h | h
      · exact ⟨fun _ => h, fun hpos => by
          have huA : u ∈ A := by rw [← h_inter, mem_inter]; exact ⟨(hD_neg_sub k) h, hpos⟩
          have := cover_inter_antichain_eq (hD_neg.1 k) hA_anti (h_mem_neg k) (he_mem k) h huA
          exact this ▸ h_mem_pos k⟩
      · exact ⟨fun hneg => by
          have huA : u ∈ A := by rw [← h_inter, mem_inter]; exact ⟨hneg, (hD_pos_sub k) h⟩
          have := cover_inter_antichain_eq (hD_pos.1 k) hA_anti (h_mem_pos k) (he_mem k) h huA
          exact this ▸ h_mem_neg k, fun _ => h⟩
    rcases (mem_union.mp hu).elim (fun h => Or.inl (hD_neg_sub i h)) (fun h => Or.inr (hD_pos_sub i h)) with hneg | hpos
    · exact (disjoint_left.mp (hD_neg.2.2 i j hij) ((hu_sub i hu).1 hneg)) ((hu_sub j hv).1 hneg)
    · exact (disjoint_left.mp (hD_pos.2.2 i j hij) ((hu_sub i hu).2 hpos)) ((hu_sub j hv).2 hpos)

lemma extend_chain_cover {m : ℕ} {S C : Finset α}
    (hCS : C ⊆ S) (hC_chain : IsChain (C : Set α))
    (C_prev : Fin m → Finset α) (hC_prev : IsChainCover (S \ C) C_prev) :
    ∃ D : Fin (m + 1) → Finset α, IsChainCover S D := by
  refine ⟨Fin.cons C C_prev, fun i => Fin.cases hC_chain (fun j => hC_prev.1 j) i, ?_, ?_⟩
  · ext x; simp only [mem_biUnion, mem_univ, true_and, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
    have : (∃ i, x ∈ C_prev i) ↔ x ∈ S \ C := by rw [← hC_prev.2.1, mem_biUnion]; simp
    rw [this, mem_sdiff]
    exact ⟨by rintro (h | ⟨hS, -⟩); exact hCS h; exact hS, fun h => if hC : x ∈ C then Or.inl hC else Or.inr ⟨h, hC⟩⟩
  · intro i j hij; rw [disjoint_iff_ne]; rintro u hu v hv rfl
    induction' i using Fin.cases with i' <;> induction' j using Fin.cases with j'
    · exact (hij rfl).elim
    · rw [Fin.cons_zero] at hu; rw [Fin.cons_succ] at hv
      have : u ∈ S \ C := by rw [← hC_prev.2.1, mem_biUnion]; exact ⟨j', mem_univ j', hv⟩
      exact (mem_sdiff.mp this).2 hu
    · rw [Fin.cons_succ] at hu; rw [Fin.cons_zero] at hv
      have : u ∈ S \ C := by rw [← hC_prev.2.1, mem_biUnion]; exact ⟨i', mem_univ i', hu⟩
      exact (mem_sdiff.mp this).2 hv
    · rw [Fin.cons_succ] at hu; rw [Fin.cons_succ] at hv
      exact disjoint_left.mp (hC_prev.2.2 i' j' (fun h => hij (congr_arg Fin.succ h))) hu hv

/-- **Dilworth's Theorem (R. P. Dilworth, 1950):**
If every antichain in a finite poset `S` has size at most `k`, then `S` can be partitioned
into `k` chains. -/
theorem dilworth_theorem (S : Finset α) (k : ℕ)
    (h_anti : ∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) :
    ∃ C : Fin k → Finset α, IsChainCover S C := by
  have h_main : ∀ n (S : Finset α) k, S.card = n →
      (∀ A ⊆ S, IsAntichain (A : Set α) → A.card ≤ k) →
      ∃ C : Fin k → Finset α, IsChainCover S C := by
    intro n; induction' n using Nat.strong_induction_on with n ih
    intro S k hn h_anti
    by_cases hk0 : k = 0
    · subst hk0
      rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp, fun i => Fin.elim0 i⟩
      · have := h_anti {x} (singleton_subset_iff.mpr hx) (isAntichain_finset_singleton x)
        simp at this
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      by_cases hn0 : n = 0
      · subst hn0; rw [Finset.card_eq_zero] at hn; subst hn
        refine ⟨fun _ => ∅, fun _ => by rw [coe_empty]; exact isChain_empty, by ext x; simp, fun _ _ _ => disjoint_empty_left _⟩
      · have hS_ne : S.Nonempty := card_pos.mp (by omega)
        rcases exists_maximal_chain S hS_ne with ⟨C, hCS, hC_ne, hC_chain, ⟨cmax, hcmax_in, hcmax_max⟩, ⟨cmin, hcmin_in, hcmin_min⟩⟩
        by_cases h_case1 : ∀ A ⊆ S \ C, IsAntichain (A : Set α) → A.card ≤ m
        · have h_card_lt : (S \ C).card < n := by
            rw [← hn, card_sdiff_of_subset hCS]; have : 0 < C.card := card_pos.mpr hC_ne; omega
          rcases ih (S \ C).card h_card_lt (S \ C) m rfl h_case1 with ⟨C_prev, hC_prev⟩
          exact extend_chain_cover hCS hC_chain C_prev hC_prev
        · have h_exists : ∃ A ⊆ S \ C, IsAntichain (A : Set α) ∧ m < A.card := by
            by_contra! h_all; exact h_case1 h_all
          rcases h_exists with ⟨A, hA_sub, hA_anti, hA_card_gt⟩
          have hAS : A ⊆ S := hA_sub.trans sdiff_subset
          have hA_card : A.card = m + 1 := by have := h_anti A hAS hA_anti; omega
          have hAC_disj : Disjoint A C := disjoint_left.mpr (fun a ha haC => (mem_sdiff.mp (hA_sub ha)).2 haC)
          have h_neg_lt : (lowerCone S A).card < n := hn ▸ lowerCone_card_lt hAS hCS hcmax_in hcmax_max hAC_disj
          have h_pos_lt : (upperCone S A).card < n := hn ▸ upperCone_card_lt hAS hCS hcmin_in hcmin_min hAC_disj
          rcases ih _ h_neg_lt (lowerCone S A) (m + 1) rfl (fun B hB => h_anti B (hB.trans (lowerCone_subset S A))) with ⟨C_neg, hC_neg⟩
          rcases ih _ h_pos_lt (upperCone S A) (m + 1) rfl (fun B hB => h_anti B (hB.trans (upperCone_subset S A))) with ⟨C_pos, hC_pos⟩
          let e_equiv : Fin (m + 1) ≃ {x // x ∈ A} := (Fin.castOrderIso hA_card.symm).toEquiv.trans (Finset.equivFin A).symm
          let e : Fin (m + 1) → α := fun i => (e_equiv i).1
          have he_inj : Function.Injective e := fun i1 i2 h => e_equiv.injective (Subtype.ext h)
          have he_mem : ∀ i, e i ∈ A := fun i => (e_equiv i).2
          rcases align_chain_cover (antichain_subset_lowerCone hAS) hA_anti e he_inj he_mem hC_neg with ⟨D_neg, hD_neg, h_mem_neg⟩
          rcases align_chain_cover (antichain_subset_upperCone hAS) hA_anti e he_inj he_mem hC_pos with ⟨D_pos, hD_pos, h_mem_pos⟩
          exact glue_chain_covers hA_anti hAS
            (lowerCone_union_upperCone S A (m + 1) hAS hA_anti hA_card h_anti)
            (lowerCone_inter_upperCone hA_anti hAS) e he_mem D_neg hD_neg h_mem_neg D_pos hD_pos h_mem_pos
  exact h_main S.card S k rfl h_anti

/-- **Dilworth's Min-Max Equivalence:**
The maximum size of an antichain equals the minimum number of chains covering the poset. -/
theorem dilworth_duality [Fintype α] (w : ℕ)
    (h_max : ∃ A : Finset α, IsAntichain (A : Set α) ∧ A.card = w)
    (h_bound : ∀ A : Finset α, IsAntichain (A : Set α) → A.card ≤ w) :
    (∃ C : Fin w → Finset α, IsChainCover Finset.univ C) ∧
    (∀ k < w, ¬ ∃ C : Fin k → Finset α, IsChainCover Finset.univ C) := by
  refine ⟨dilworth_theorem univ w (fun A _ => h_bound A), ?_⟩
  rintro k hk ⟨C, hC⟩
  rcases h_max with ⟨A, hA_anti, hA_card⟩
  have h_cov : A ⊆ Finset.biUnion Finset.univ (fun i => A ∩ C i) := fun x hx => by
    have : x ∈ Finset.biUnion univ C := by rw [hC.2.1]; exact mem_univ x
    rcases mem_biUnion.mp this with ⟨i, -, hi⟩
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_inter.mpr ⟨hx, hi⟩⟩
  have h_sum := (card_le_card h_cov).trans card_biUnion_le
  have h_sum_le : (Finset.univ : Finset (Fin k)).sum (fun i => (A ∩ C i).card) ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 1) :=
    sum_le_sum (fun i _ => by rw [inter_comm]; exact chain_inter_antichain_card_le_one (C i) A (hC.1 i) hA_anti)
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h_sum_le
  have : w ≤ k := hA_card ▸ h_sum.trans h_sum_le
  omega

#print axioms dilworth_theorem
#print axioms dilworth_duality

/-- The collection of subchains of `S` that have `x` as their maximum element. -/
noncomputable def chainsEndingAt (S : Finset α) (x : α) : Finset (Finset α) :=
  S.powerset.filter (fun C => x ∈ C ∧ (∀ y ∈ C, y ≤ x) ∧ IsChain (C : Set α))

lemma singleton_mem_chainsEndingAt {S : Finset α} {x : α} (hx : x ∈ S) :
    {x} ∈ chainsEndingAt S x := by
  rw [chainsEndingAt, mem_filter, mem_powerset, singleton_subset_iff]
  exact ⟨hx, mem_singleton_self x, fun y hy => (mem_singleton.mp hy).le, isChain_finset_singleton x⟩

lemma chainsEndingAt_nonempty {S : Finset α} {x : α} (hx : x ∈ S) :
    (chainsEndingAt S x).Nonempty :=
  ⟨{x}, singleton_mem_chainsEndingAt hx⟩

/-- The height of an element `x ∈ S` is the maximum length of a chain in `S` ending at `x`. -/
noncomputable def posetHeight (S : Finset α) (x : α) : ℕ :=
  (chainsEndingAt S x).sup Finset.card

lemma posetHeight_ge_one {S : Finset α} {x : α} (hx : x ∈ S) :
    1 ≤ posetHeight S x := by
  have := Finset.le_sup (f := Finset.card) (singleton_mem_chainsEndingAt hx)
  rwa [card_singleton] at this

lemma posetHeight_le {S : Finset α} {x : α} {m : ℕ}
    (h_chain : ∀ C ⊆ S, IsChain (C : Set α) → C.card ≤ m) :
    posetHeight S x ≤ m :=
  Finset.sup_le (fun C hC => by simp only [chainsEndingAt, mem_filter, mem_powerset] at hC; exact h_chain C hC.1 hC.2.2.2)

lemma posetHeight_lt_of_lt {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    posetHeight S x < posetHeight S y := by
  rcases Finset.exists_max_image (chainsEndingAt S x) Finset.card (chainsEndingAt_nonempty hx) with ⟨C, hC_in, hC_max⟩
  have hC_height : C.card = posetHeight S x := le_antisymm (Finset.le_sup hC_in) (Finset.sup_le hC_max)
  rw [chainsEndingAt, mem_filter, mem_powerset] at hC_in
  rcases hC_in with ⟨hCS, -, hC_le_x, hC_chain⟩
  have hy_not : y ∉ C := fun h => (not_lt_of_ge (hC_le_x y h)) hxy
  have hC'_chain : IsChain ((insert y C : Finset α) : Set α) := by
    intro u v hu hv; simp only [mem_coe, mem_insert] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact Or.inl le_rfl
    · exact Or.inr ((hC_le_x v hv).trans hxy.le)
    · exact Or.inl ((hC_le_x u hu).trans hxy.le)
    · exact hC_chain u v hu hv
  have hC'_in : insert y C ∈ chainsEndingAt S y := by
    rw [chainsEndingAt, mem_filter, mem_powerset]
    refine ⟨insert_subset hy hCS, mem_insert_self y C, fun z hz => ?_, hC'_chain⟩
    exact (mem_insert.mp hz).elim (fun e => e ▸ le_rfl) (fun hz => (hC_le_x z hz).trans hxy.le)
  have h_le : (insert y C).card ≤ posetHeight S y := Finset.le_sup (f := Finset.card) hC'_in
  rw [card_insert_of_notMem hy_not, hC_height] at h_le; omega

/-- **Mirsky's Theorem (Dual Dilworth Theorem, L. Mirsky, 1971):**
If every chain in a finite poset `S` has size at most `m`, then `S` can be partitioned
into `m` antichains. -/
theorem mirsky_theorem (S : Finset α) (m : ℕ)
    (h_chain : ∀ C ⊆ S, IsChain (C : Set α) → C.card ≤ m) :
    ∃ A : Fin m → Finset α, IsAntichainCover S A := by
  by_cases hm : m = 0
  · subst hm
    have : S = ∅ := by
      by_contra! h; rcases h with ⟨x, hx⟩
      have := (posetHeight_ge_one hx).trans (posetHeight_le h_chain (x := x)); omega
    subst this
    refine ⟨fun _ => ∅, fun _ => by rw [coe_empty]; exact isAntichain_empty, by simp, fun _ _ _ => disjoint_empty_left _⟩
  · let A : Fin m → Finset α := fun i => S.filter (fun x => posetHeight S x = i.val + 1)
    refine ⟨A, ?_, ?_, ?_⟩
    · intro i u v hu hv hne
      simp only [mem_coe, mem_filter, A] at hu hv
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := posetHeight_lt_of_lt hu.1 hv.1 (lt_of_le_of_ne h hne); omega
      · have := posetHeight_lt_of_lt hv.1 hu.1 (lt_of_le_of_ne h hne.symm); omega
    · ext x; simp only [mem_biUnion, mem_univ, true_and, mem_filter, A]
      refine ⟨fun ⟨i, hxS, _⟩ => hxS, fun hxS => ?_⟩
      have h1 := posetHeight_ge_one hxS
      have hm_ge := posetHeight_le h_chain (x := x)
      exact ⟨⟨posetHeight S x - 1, by omega⟩, hxS, by dsimp; omega⟩
    · intro i j hij
      rw [disjoint_iff_ne]; rintro u hu _ hv rfl
      simp only [mem_filter, A] at hu hv
      exact hij (Fin.ext (by omega))

/-- **Mirsky's Min-Max Equivalence (Dual Dilworth Duality):**
The maximum size of a chain equals the minimum number of antichains covering the poset. -/
theorem mirsky_duality [Fintype α] (c : ℕ)
    (h_max : ∃ C : Finset α, IsChain (C : Set α) ∧ C.card = c)
    (h_bound : ∀ C : Finset α, IsChain (C : Set α) → C.card ≤ c) :
    (∃ A : Fin c → Finset α, IsAntichainCover Finset.univ A) ∧
    (∀ k < c, ¬ ∃ A : Fin k → Finset α, IsAntichainCover Finset.univ A) := by
  refine ⟨mirsky_theorem univ c (fun C _ => h_bound C), ?_⟩
  rintro k hk ⟨A, hA⟩
  rcases h_max with ⟨C, hC_chain, hC_card⟩
  have h_cov : C ⊆ Finset.biUnion Finset.univ (fun i => C ∩ A i) := fun x hx => by
    have : x ∈ Finset.biUnion univ A := by rw [hA.2.1]; exact mem_univ x
    rcases mem_biUnion.mp this with ⟨i, -, hi⟩
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_inter.mpr ⟨hx, hi⟩⟩
  have h_sum := (card_le_card h_cov).trans card_biUnion_le
  have h_sum_le : (Finset.univ : Finset (Fin k)).sum (fun i => (C ∩ A i).card) ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 1) :=
    sum_le_sum (fun i _ => chain_inter_antichain_card_le_one C (A i) hC_chain (hA.1 i))
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h_sum_le
  have : c ≤ k := hC_card ▸ h_sum.trans h_sum_le
  omega

#print axioms mirsky_theorem
#print axioms mirsky_duality

end DilworthTheorem
