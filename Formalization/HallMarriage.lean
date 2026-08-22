import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Hall's Marriage Theorem (Freek Wiedijk #87)

This module provides the formalization for **Hall's Marriage Theorem** /
Hall's Marriage Condition on Systems of Distinct Representatives (P. Hall, 1935).

## Mathematical Statement
Let $A_1, \dots, A_n$ be a finite family of finite sets indexed by a finite type $\iota$.
A **System of Distinct Representatives (SDR)** (or transversal) is an injective choice function
$f : \iota \to \alpha$ such that $\forall i \in \iota, f(i) \in A_i$.

**Hall's Theorem:** A system of distinct representatives exists if and only if **Hall's Marriage Condition**
holds: for every subset of indices $J \subseteq \iota$,
$$\left| \bigcup_{i \in J} A_i \right| \ge |J|$$

## References
* P. Hall (1935), *On Representatives of Subsets*, J. London Math. Soc., 10(1):26–30.
* P. R. Halmos & H. E. Vaughan (1950), *The Marriage Problem*, Amer. J. Math., 72(1):214–215.
* F. Wiedijk (2008), *Formalizing 100 Theorems*, #87.
-/

namespace HallMarriage

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α] [Fintype ι]

/-- Hall's marriage condition: for every subset of indices `J`, the union of sets `A i` for `i ∈ J`
has cardinality at least `|J|`. -/
def HallCondition (A : ι → Finset α) : Prop :=
  ∀ J : Finset ι, J.card ≤ (J.biUnion A).card

/-- A System of Distinct Representatives (SDR) / Transversal for the indexed family `A`. -/
def IsSDR (A : ι → Finset α) (f : ι → α) : Prop :=
  Function.Injective f ∧ ∀ i : ι, f i ∈ A i

/-- **Hall's Marriage Theorem (Necessity):**
If a system of distinct representatives exists, then Hall's condition holds. -/
theorem hall_marriage_necessary (A : ι → Finset α) (f : ι → α) (hf : IsSDR A f) :
    HallCondition A := by
  intro J
  have h_sub : J.image f ⊆ J.biUnion A := by
    intro x hx
    rw [mem_image] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [mem_biUnion]
    exact ⟨i, hi, hf.2 i⟩
  have h_card := card_le_card h_sub
  rw [card_image_of_injective J hf.1] at h_card
  exact h_card

lemma biUnion_sdiff (J : Finset ι) (A : ι → Finset α) (T : Finset α) :
    (J.biUnion (fun i => A i \ T)) = (J.biUnion A) \ T := by
  ext x
  simp only [mem_biUnion, mem_sdiff]
  constructor
  · rintro ⟨i, hi, hx1, hx2⟩
    exact ⟨⟨i, hi, hx1⟩, hx2⟩
  · rintro ⟨⟨i, hi, hx1⟩, hx2⟩
    exact ⟨i, hi, hx1, hx2⟩

lemma union_sdiff_self_right (U T : Finset α) : (U ∪ T) \ T = U \ T := by
  ext x
  simp only [mem_sdiff, mem_union]
  tauto

lemma card_sdiff_singleton_ge (U : Finset α) (x : α) :
    U.card - 1 ≤ (U \ {x}).card := by
  by_cases hx : x ∈ U
  · rw [sdiff_singleton_eq_erase, card_erase_of_mem hx]
  · have hdisj : Disjoint U {x} := by rwa [disjoint_singleton_right]
    rw [sdiff_eq_self_of_disjoint hdisj]
    exact Nat.sub_le U.card 1

lemma hall_marriage_finset [Nonempty α] (n : ℕ) (A : ι → Finset α) (S : Finset ι) (hn : S.card = n)
    (h_hall : ∀ J ⊆ S, J.card ≤ (J.biUnion A).card) :
    ∃ f : ι → α, (∀ i ∈ S, f i ∈ A i) ∧ (∀ i ∈ S, ∀ j ∈ S, f i = f j → i = j) := by
  induction' n using Nat.strong_induction_on with n ih generalizing S A
  by_cases hn0 : n = 0
  · subst hn0
    rw [Finset.card_eq_zero] at hn
    subst hn
    inhabit α
    refine ⟨fun _ => default, by simp, by simp⟩
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    by_cases h_tight : ∃ J0 ⊆ S, 0 < J0.card ∧ J0.card < n ∧ (J0.biUnion A).card = J0.card
    · rcases h_tight with ⟨J0, hJ0_sub, hJ0_pos, hJ0_lt, hJ0_eq⟩
      have h_hall_J0 : ∀ J ⊆ J0, J.card ≤ (J.biUnion A).card := fun J hJ => h_hall J (hJ.trans hJ0_sub)
      rcases ih J0.card hJ0_lt A J0 rfl h_hall_J0 with ⟨f1, hf1_mem, hf1_inj⟩
      let T : Finset α := J0.biUnion A
      have h_im_sub : J0.image f1 ⊆ T := by
        intro x hx
        rcases mem_image.mp hx with ⟨i, hi, rfl⟩
        exact mem_biUnion.mpr ⟨i, hi, hf1_mem i hi⟩
      have h_im_card : (J0.image f1).card = J0.card := card_image_of_injOn hf1_inj
      have h_im_eq : J0.image f1 = T := by
        apply eq_of_subset_of_card_le h_im_sub
        rw [h_im_card, hJ0_eq]
      let K : Finset ι := S \ J0
      have hK_card : K.card = n - J0.card := by
        rw [← hn, card_sdiff, inter_eq_left.mpr hJ0_sub]
      have hK_lt : K.card < n := by
        omega
      let A' : ι → Finset α := fun i => A i \ T
      have h_hall_K : ∀ J ⊆ K, J.card ≤ (J.biUnion A').card := by
        intro J hJ
        have hJ_disj : Disjoint J J0 := by
          rw [disjoint_iff_ne]
          intro i hi j hj
          have : i ∈ S \ J0 := hJ hi
          rw [mem_sdiff] at this
          rintro rfl
          exact this.2 hj
        have h_union_sub : J ∪ J0 ⊆ S := by
          apply union_subset (hJ.trans (sdiff_subset)) hJ0_sub
        have h_hall_union := h_hall (J ∪ J0) h_union_sub
        rw [card_union_of_disjoint hJ_disj] at h_hall_union
        rw [union_biUnion] at h_hall_union
        have h_sdiff_card : (((J.biUnion A) ∪ T) \ T).card = ((J.biUnion A) ∪ T).card - T.card := by
          rw [card_sdiff, inter_eq_left.mpr subset_union_right]
        rw [union_sdiff_self_right] at h_sdiff_card
        rw [← biUnion_sdiff] at h_sdiff_card
        rw [h_sdiff_card]
        have h_union_T : (J.biUnion A ∪ J0.biUnion A) = (J.biUnion A ∪ T) := rfl
        rw [h_union_T] at h_hall_union
        have hT_card : T.card = J0.card := hJ0_eq
        rw [hT_card]
        omega
      rcases ih K.card hK_lt A' K rfl h_hall_K with ⟨f2, hf2_mem, hf2_inj⟩
      let f : ι → α := fun i => if i ∈ J0 then f1 i else f2 i
      refine ⟨f, ?_, ?_⟩
      · intro i hi
        dsimp [f]
        split_ifs with hiJ0
        · exact hf1_mem i hiJ0
        · have hiK : i ∈ K := mem_sdiff.mpr ⟨hi, hiJ0⟩
          have := hf2_mem i hiK
          rw [mem_sdiff] at this
          exact this.1
      · intro i hi j hj hfeq
        dsimp [f] at hfeq
        by_cases hiJ0 : i ∈ J0 <;> by_cases hjJ0 : j ∈ J0
        · simp only [hiJ0, hjJ0, ↓reduceIte] at hfeq
          exact hf1_inj i hiJ0 j hjJ0 hfeq
        · simp only [hiJ0, hjJ0, ↓reduceIte] at hfeq
          exfalso
          have h1 : f1 i ∈ T := by
            rw [← h_im_eq]
            exact mem_image_of_mem f1 hiJ0
          have hjK : j ∈ K := mem_sdiff.mpr ⟨hj, hjJ0⟩
          have h2 := hf2_mem j hjK
          rw [mem_sdiff] at h2
          rw [hfeq] at h1
          exact h2.2 h1
        · simp only [hiJ0, hjJ0, ↓reduceIte] at hfeq
          exfalso
          have h1 : f1 j ∈ T := by
            rw [← h_im_eq]
            exact mem_image_of_mem f1 hjJ0
          have hiK : i ∈ K := mem_sdiff.mpr ⟨hi, hiJ0⟩
          have h2 := hf2_mem i hiK
          rw [mem_sdiff] at h2
          rw [← hfeq] at h1
          exact h2.2 h1
        · simp only [hiJ0, hjJ0, ↓reduceIte] at hfeq
          have hiK : i ∈ K := mem_sdiff.mpr ⟨hi, hiJ0⟩
          have hjK : j ∈ K := mem_sdiff.mpr ⟨hj, hjJ0⟩
          exact hf2_inj i hiK j hjK hfeq
    · have hS_nonempty : S.Nonempty := by
        rw [← card_pos, hn]
        exact hn_pos
      rcases hS_nonempty with ⟨i0, hi0⟩
      have h_sing_sub : {i0} ⊆ S := singleton_subset_iff.mpr hi0
      have h_sing_hall := h_hall {i0} h_sing_sub
      rw [card_singleton, singleton_biUnion] at h_sing_hall
      have hAi0_nonempty : (A i0).Nonempty := by
        rw [← card_pos]
        exact lt_of_lt_of_le Nat.zero_lt_one h_sing_hall
      rcases hAi0_nonempty with ⟨x, hx⟩
      let K : Finset ι := S \ {i0}
      have hK_card : K.card = n - 1 := by
        rw [← hn, card_sdiff, inter_eq_left.mpr h_sing_sub, card_singleton]
      have hK_lt : K.card < n := by omega
      let A' : ι → Finset α := fun i => A i \ {x}
      have h_hall_K : ∀ J ⊆ K, J.card ≤ (J.biUnion A').card := by
        intro J hJ
        by_cases hJ_empty : J = ∅
        · subst hJ_empty
          simp
        · have hJ_pos : 0 < J.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hJ_empty)
          have hJ_sub_S : J ⊆ S := hJ.trans (sdiff_subset)
          have hi0_not_in_J : i0 ∉ J := fun hi0J => (mem_sdiff.mp (hJ hi0J)).2 (mem_singleton_self i0)
          have hJ_lt : J.card < n := by
            have : J ⊂ S := by
              rw [Finset.ssubset_iff_subset_ne]
              refine ⟨hJ_sub_S, ?_⟩
              rintro rfl
              exact hi0_not_in_J hi0
            rw [← hn]
            exact card_lt_card this
          have h_ne : (J.biUnion A).card ≠ J.card := fun heq =>
            h_tight ⟨J, hJ_sub_S, hJ_pos, hJ_lt, heq⟩
          have h_le := h_hall J hJ_sub_S
          have h_gt : J.card < (J.biUnion A).card := lt_of_le_of_ne h_le h_ne.symm
          rw [biUnion_sdiff]
          have h_sdiff := card_sdiff_singleton_ge (J.biUnion A) x
          omega
      rcases ih K.card hK_lt A' K rfl h_hall_K with ⟨f0, hf0_mem, hf0_inj⟩
      let f : ι → α := fun i => if i = i0 then x else f0 i
      refine ⟨f, ?_, ?_⟩
      · intro i hi
        dsimp [f]
        split_ifs with heq
        · subst heq
          exact hx
        · have hiK : i ∈ K := by
            rw [mem_sdiff, mem_singleton]
            exact ⟨hi, heq⟩
          have := hf0_mem i hiK
          rw [mem_sdiff] at this
          exact this.1
      · intro i hi j hj hfeq
        dsimp [f] at hfeq
        by_cases hi_eq : i = i0 <;> by_cases hj_eq : j = i0
        · rw [hi_eq, hj_eq]
        · simp only [hi_eq, hj_eq, ↓reduceIte] at hfeq
          subst hi_eq
          exfalso
          have hjK : j ∈ K := by
            rw [mem_sdiff, mem_singleton]
            exact ⟨hj, hj_eq⟩
          have h2 := hf0_mem j hjK
          rw [mem_sdiff, mem_singleton] at h2
          exact h2.2 hfeq.symm
        · simp only [hi_eq, hj_eq, ↓reduceIte] at hfeq
          subst hj_eq
          exfalso
          have hiK : i ∈ K := by
            rw [mem_sdiff, mem_singleton]
            exact ⟨hi, hi_eq⟩
          have h2 := hf0_mem i hiK
          rw [mem_sdiff, mem_singleton] at h2
          exact h2.2 hfeq
        · simp only [hi_eq, hj_eq, ↓reduceIte] at hfeq
          have hiK : i ∈ K := by
            rw [mem_sdiff, mem_singleton]
            exact ⟨hi, hi_eq⟩
          have hjK : j ∈ K := by
            rw [mem_sdiff, mem_singleton]
            exact ⟨hj, hj_eq⟩
          exact hf0_inj i hiK j hjK hfeq

/-- **Hall's Marriage Theorem (Sufficiency / Equivalence, Freek Wiedijk #87):**
A finite collection of sets admits a system of distinct representatives if and only if
it satisfies Hall's condition. -/
theorem hall_marriage_theorem (A : ι → Finset α) :
    (∃ f : ι → α, IsSDR A f) ↔ HallCondition A := by
  constructor
  · rintro ⟨f, hf⟩
    exact hall_marriage_necessary A f hf
  · intro hH
    by_cases h_empty : IsEmpty ι
    · haveI := h_empty
      refine ⟨fun i => (IsEmpty.false i).elim, ?_⟩
      exact ⟨fun i => (IsEmpty.false i).elim, fun i => (IsEmpty.false i).elim⟩
    · rw [not_isEmpty_iff] at h_empty
      haveI : Nonempty ι := h_empty
      have i0 : ι := Classical.choice h_empty
      have h_sing := hH {i0}
      rw [card_singleton, singleton_biUnion] at h_sing
      have hA_pos : 0 < (A i0).card := lt_of_lt_of_le Nat.zero_lt_one h_sing
      have hA_nonempty : (A i0).Nonempty := card_pos.mp hA_pos
      rcases hA_nonempty with ⟨x0, _⟩
      haveI : Nonempty α := ⟨x0⟩
      rcases hall_marriage_finset (Finset.univ.card) A Finset.univ rfl (fun J _ => hH J) with ⟨f, hf_mem, hf_inj⟩
      refine ⟨f, ?_, fun i => hf_mem i (mem_univ i)⟩
      intro i j hij
      exact hf_inj i (mem_univ i) j (mem_univ j) hij

#print axioms hall_marriage_theorem

/-- An edge in the bipartite incidence graph between `ι` and `α` given by family `A`. -/
def IsIncidenceEdge (A : ι → Finset α) (e : ι × α) : Prop :=
  e.2 ∈ A e.1

/-- A matching in the bipartite incidence graph is a set of edges `M ⊆ ι × α` such that
no two distinct edges share a vertex in `ι` or in `α`. -/
def IsMatching (A : ι → Finset α) (M : Finset (ι × α)) : Prop :=
  (∀ e ∈ M, IsIncidenceEdge A e) ∧
  (∀ e1 ∈ M, ∀ e2 ∈ M, e1.1 = e2.1 → e1 = e2) ∧
  (∀ e1 ∈ M, ∀ e2 ∈ M, e1.2 = e2.2 → e1 = e2)

/-- A vertex cover in the bipartite incidence graph is a pair of subsets $(C_ι, C_α)$
such that every edge $a \in A i$ has $i \in C_ι$ or $a \in C_α$. -/
def IsVertexCover (A : ι → Finset α) (C : Finset ι × Finset α) : Prop :=
  ∀ i : ι, ∀ a ∈ A i, i ∈ C.1 ∨ a ∈ C.2

/-- **Weak Kőnig Duality:**
The cardinality of any matching in the bipartite incidence graph is at most
the cardinality of any vertex cover. -/
theorem matching_card_le_vertexCover_card (A : ι → Finset α)
    (M : Finset (ι × α)) (hM : IsMatching A M)
    (C : Finset ι × Finset α) (hC : IsVertexCover A C) :
    M.card ≤ C.1.card + C.2.card := by
  let M1 := M.filter (fun e => e.1 ∈ C.1)
  let M2 := M.filter (fun e => e.2 ∈ C.2)
  have hM_sub : M ⊆ M1 ∪ M2 := by
    intro e he
    rw [mem_union, mem_filter, mem_filter]
    have he_inc := hM.1 e he
    rcases hC e.1 e.2 he_inc with h1 | h2
    · exact Or.inl ⟨he, h1⟩
    · exact Or.inr ⟨he, h2⟩
  have h_le := (card_le_card hM_sub).trans (card_union_le M1 M2)
  have hM1_le : M1.card ≤ C.1.card := by
    have h_im : M1.image Prod.fst ⊆ C.1 := by
      intro x hx
      rw [mem_image] at hx
      rcases hx with ⟨e, he, rfl⟩
      exact (mem_filter.mp he).2
    have h_card := card_le_card h_im
    rw [card_image_of_injOn (fun e1 he1 e2 he2 heq => hM.2.1 e1 (mem_filter.mp he1).1 e2 (mem_filter.mp he2).1 heq)] at h_card
    exact h_card
  have hM2_le : M2.card ≤ C.2.card := by
    have h_im : M2.image Prod.snd ⊆ C.2 := by
      intro x hx
      rw [mem_image] at hx
      rcases hx with ⟨e, he, rfl⟩
      exact (mem_filter.mp he).2
    have h_card := card_le_card h_im
    rw [card_image_of_injOn (fun e1 he1 e2 he2 heq => hM.2.2 e1 (mem_filter.mp he1).1 e2 (mem_filter.mp he2).1 heq)] at h_card
    exact h_card
  omega

/-- An SDR directly gives a perfect matching covering all vertices of `ι` in the incidence graph. -/
theorem sdr_to_perfect_matching (A : ι → Finset α) (f : ι → α) (hf : IsSDR A f) :
    ∃ M : Finset (ι × α), IsMatching A M ∧ M.card = Fintype.card ι := by
  let M : Finset (ι × α) := (Finset.univ : Finset ι).image (fun i => (i, f i))
  have hM_card : M.card = Fintype.card ι := by
    rw [card_image_of_injective _ (fun _ _ h => (Prod.ext_iff.mp h).1), card_univ]
  refine ⟨M, ⟨?_, ?_, ?_⟩, hM_card⟩
  · rintro ⟨i, a⟩ he
    rw [mem_image] at he
    rcases he with ⟨i', -, heq⟩
    injection heq with hi ha
    subst hi ha
    exact hf.2 i'
  · intro e1 he1 e2 he2 heq
    rw [mem_image] at he1 he2
    rcases he1 with ⟨i1, -, rfl⟩
    rcases he2 with ⟨i2, -, rfl⟩
    dsimp at heq
    subst heq
    rfl
  · intro e1 he1 e2 he2 heq
    rw [mem_image] at he1 he2
    rcases he1 with ⟨i1, -, rfl⟩
    rcases he2 with ⟨i2, -, rfl⟩
    dsimp at heq
    have hi := hf.1 heq
    subst hi
    rfl

/-- **Hall's Matching Equivalence:**
A bipartite incidence graph has a matching covering `ι` if and only if Hall's condition holds. -/
theorem hall_matching_theorem (A : ι → Finset α) :
    (∃ M : Finset (ι × α), IsMatching A M ∧ M.card = Fintype.card ι) ↔ HallCondition A := by
  constructor
  · rintro ⟨M, hM, hM_card⟩
    have h_fst_inj : Set.InjOn Prod.fst (M : Set (ι × α)) :=
      fun e1 he1 e2 he2 heq => hM.2.1 e1 he1 e2 he2 heq
    have h_im_univ : M.image Prod.fst = Finset.univ := by
      apply eq_univ_of_card
      simp [card_image_of_injOn h_fst_inj, hM_card]
    have h_unique : ∀ i : ι, ∃! a : α, (i, a) ∈ M := by
      intro i
      have h_in_univ : i ∈ (Finset.univ : Finset ι) := mem_univ i
      rw [← h_im_univ, mem_image] at h_in_univ
      rcases h_in_univ with ⟨⟨i', a⟩, he, rfl⟩
      refine ⟨a, he, ?_⟩
      intro a' ha'
      have heq := hM.2.1 (i', a') ha' (i', a) he rfl
      cases heq
      rfl
    let f : ι → α := fun i => (h_unique i).choose
    have hf_mem_M : ∀ i : ι, (i, f i) ∈ M := fun i => (h_unique i).choose_spec.1
    have hf_mem_A : ∀ i : ι, f i ∈ A i := fun i => hM.1 (i, f i) (hf_mem_M i)
    have hf_inj : Function.Injective f := by
      intro i j heq
      have he1 : (i, f i) ∈ M := hf_mem_M i
      have he2 : (j, f j) ∈ M := hf_mem_M j
      rw [heq] at he1
      have heq' := hM.2.2 (i, f j) he1 (j, f j) he2 rfl
      cases heq'
      rfl
    have h_sdr : IsSDR A f := ⟨hf_inj, hf_mem_A⟩
    exact hall_marriage_necessary A f h_sdr
  · intro hH
    rcases (hall_marriage_theorem A).mpr hH with ⟨f, hf⟩
    exact sdr_to_perfect_matching A f hf

#print axioms hall_matching_theorem
#print axioms matching_card_le_vertexCover_card

end HallMarriage


