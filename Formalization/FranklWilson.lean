import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# Frankl–Wilson Theorem on Modulo-p Intersecting Families (1981)

**The Frankl–Wilson Theorem (Péter Frankl & Richard M. Wilson, 1981)** is a landmark triumph
of the linear algebra method in extremal combinatorics.

## Mathematical Statement
Let $p$ be a prime, and let $L \subset \{0, 1, \dots, p-1\}$ be a set of $s = |L|$ residues modulo $p$.
Let $\mathcal{F}$ be a family of subsets of an $n$-element universe such that:
1. $|A| \pmod p \notin L$ for all $A \in \mathcal{F}$
2. $|A \cap B| \pmod p \in L$ for all distinct $A \ne B \in \mathcal{F}$.

Then the family size satisfies the polynomial dimension bound:
$$|\mathcal{F}| \le \sum_{i=0}^s \binom{n}{i}$$

When all subsets in $\mathcal{F}$ have the same uniform cardinality $k$, the bound sharpens to:
$$|\mathcal{F}| \le \binom{n}{s}$$

## Applications & Borsuk's Conjecture
In 1993, Jeff Kahn and Gil Kalai utilized the Frankl–Wilson theorem to construct high-dimensional
point sets in $\mathbb{R}^d$ that require exponentially many pieces to partition into sets of
smaller diameter, famously **disproving Borsuk's Conjecture (1933)**.
-/

-- ============================================================================
-- Section 1: Modulo-p Intersection Families
-- ============================================================================

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of subsets whose pairwise intersection cardinalities mod p lie in L. -/
structure ModuloPIntersectingFamily (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p)) where
  /-- The family of subsets -/
  F : Finset (Finset α)
  /-- Forbidden self-size residue: |A| mod p ∉ L -/
  h_self : ∀ A ∈ F, (A.card : ZMod p) ∉ L
  /-- Allowed pairwise intersection residues: |A ∩ B| mod p ∈ L for A ≠ B -/
  h_inter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L

-- ============================================================================
-- Section 2: Monomials and Characteristic Evaluations
-- ============================================================================

/-- Characteristic monomial function associated with subset `I`: returns 1 if `I ⊆ B`, else 0. -/
def monomial (p : ℕ) (I : Finset α) (B : Finset α) : ZMod p :=
  if I ⊆ B then 1 else 0

lemma monomial_empty (p : ℕ) (B : Finset α) : monomial p ∅ B = 1 := by
  simp [monomial]

lemma monomial_union (p : ℕ) (I J B : Finset α) :
    monomial p (I ∪ J) B = monomial p I B * monomial p J B := by
  simp only [monomial, union_subset_iff]
  by_cases hI : I ⊆ B <;> by_cases hJ : J ⊆ B <;> simp [hI, hJ]

lemma monomial_singleton (p : ℕ) (i : α) (B : Finset α) :
    monomial p {i} B = if i ∈ B then 1 else 0 := by
  simp [monomial, singleton_subset_iff]

lemma sum_monomial_singleton (p : ℕ) (A B : Finset α) :
    (∑ i ∈ A, monomial p {i} B) = ((A ∩ B).card : ZMod p) := by
  simp_rw [monomial_singleton]
  have h_filter : (∑ i ∈ A, (if i ∈ B then (1 : ZMod p) else 0)) =
      ∑ i ∈ A.filter (· ∈ B), (1 : ZMod p) := by
    rw [sum_filter]
  rw [h_filter, sum_const, nsmul_eq_mul, mul_one]
  have h_eq : A.filter (· ∈ B) = A ∩ B := by
    ext x
    simp [mem_filter, mem_inter]
  rw [h_eq]


-- ============================================================================
-- Section 3: Evaluation Polynomials and Linear Independence
-- ============================================================================

/-- The polynomial evaluation function F_A(B) = ∏_{l ∈ L} (|A ∩ B| - l) mod p. -/
def evalPoly (p : ℕ) (L : Finset (ZMod p)) (A : Finset α) (B : Finset α) : ZMod p :=
  ∏ l ∈ L, (((A ∩ B).card : ZMod p) - l)

lemma evalPoly_self_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L) (A : Finset α) (hA : A ∈ fam.F) :
    evalPoly p L A A ≠ 0 := by
  dsimp [evalPoly]
  rw [inter_self]
  intro h_zero
  obtain ⟨l, hl, heq⟩ := prod_eq_zero_iff.mp h_zero
  have h_sub : (A.card : ZMod p) = l := sub_eq_zero.mp heq
  have hl_in : (A.card : ZMod p) ∈ L := by
    rw [h_sub]
    exact hl
  exact fam.h_self A hA hl_in


lemma evalPoly_other_eq_zero (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L) (A B : Finset α)
    (hA : A ∈ fam.F) (hB : B ∈ fam.F) (hne : A ≠ B) :
    evalPoly p L A B = 0 := by
  dsimp [evalPoly]
  have hl_mem : ((A ∩ B).card : ZMod p) ∈ L := fam.h_inter A hA B hB hne
  exact prod_eq_zero hl_mem (sub_self _)

lemma evalPoly_linearIndependent (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L) :
    LinearIndependent (ZMod p) (fun (A : fam.F) ↦ (evalPoly p L A.1 : (Finset α → ZMod p))) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h_eval : (∑ A ∈ s, g A • (evalPoly p L A.1 : Finset α → ZMod p)) i.1 = 0 := by
    rw [hg]
    rfl
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h_eval
  have h_single : (∑ A ∈ s, g A * evalPoly p L A.1 i.1) = g i * evalPoly p L i.1 i.1 := by
    apply sum_eq_single i
    · intro A _ hAi
      have hne : (A : Finset α) ≠ i.1 := by
        intro heq
        exact hAi (Subtype.ext heq)
      rw [evalPoly_other_eq_zero p L fam A.1 i.1 A.2 i.2 hne, mul_zero]
    · intro h_not_mem
      exact False.elim (h_not_mem hi)
  rw [h_single] at h_eval
  have h_nz := evalPoly_self_ne_zero p L fam i.1 i.2
  cases mul_eq_zero.mp h_eval with
  | inl hg_zero => exact hg_zero
  | inr h_zero => exact False.elim (h_nz h_zero)


-- ============================================================================
-- Section 4: Subspace of Bounded Degree Monomials
-- ============================================================================

/-- Submodule of (Finset α → ZMod p) spanned by monomials of size at most `d`. -/
def degSubmodule (p : ℕ) (d : ℕ) : Submodule (ZMod p) (Finset α → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun (I : {I : Finset α // I.card ≤ d}) ↦ (monomial p I.1 : Finset α → ZMod p)))

lemma monomial_mem_degSubmodule (p : ℕ) {I : Finset α} {d : ℕ} (h : I.card ≤ d) :
    (monomial p I : Finset α → ZMod p) ∈ degSubmodule (α := α) p d := by
  apply Submodule.subset_span
  exact ⟨⟨I, h⟩, rfl⟩

lemma one_mem_degSubmodule (p : ℕ) (d : ℕ) :
    (1 : Finset α → ZMod p) ∈ degSubmodule (α := α) p d := by
  have h_empty : (monomial p ∅ : Finset α → ZMod p) = 1 := by
    ext B
    exact monomial_empty p B
  rw [← h_empty]
  exact monomial_mem_degSubmodule p (by simp)

lemma const_mem_degSubmodule (p : ℕ) (c : ZMod p) (d : ℕ) :
    (fun _ ↦ c : Finset α → ZMod p) ∈ degSubmodule (α := α) p d := by
  have h_smul : (fun _ ↦ c : Finset α → ZMod p) = c • (1 : Finset α → ZMod p) := by
    ext B
    simp
  rw [h_smul]
  exact Submodule.smul_mem (degSubmodule p d) c (one_mem_degSubmodule p d)

lemma singleton_mem_degSubmodule (p : ℕ) (i : α) (d : ℕ) (hd : 1 ≤ d) :
    (monomial p {i} : Finset α → ZMod p) ∈ degSubmodule (α := α) p d := by
  apply monomial_mem_degSubmodule
  rw [card_singleton]
  exact hd

lemma card_inter_sub_const_mem_degSubmodule (p : ℕ) (A : Finset α) (l : ZMod p) :
    (fun B ↦ ((A ∩ B).card : ZMod p) - l : Finset α → ZMod p) ∈ degSubmodule (α := α) p 1 := by
  have h_eq : (fun B ↦ ((A ∩ B).card : ZMod p) - l : Finset α → ZMod p) =
      (∑ i ∈ A, (monomial p {i} : Finset α → ZMod p)) - (fun _ ↦ l) := by
    ext B
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [sum_monomial_singleton]
  rw [h_eq]
  refine Submodule.sub_mem _ ?_ (const_mem_degSubmodule p l 1)
  apply Submodule.sum_mem
  intro i _
  exact singleton_mem_degSubmodule p i 1 le_rfl

lemma mul_mem_degSubmodule (p : ℕ) {f g : Finset α → ZMod p} {d1 d2 : ℕ}
    (hf : f ∈ degSubmodule (α := α) p d1) (hg : g ∈ degSubmodule (α := α) p d2) :
    f * g ∈ degSubmodule (α := α) p (d1 + d2) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨I, hI⟩, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨J, hJ⟩, rfl⟩ := hg
      have h_prod : (monomial p I : Finset α → ZMod p) * monomial p J = monomial p (I ∪ J) := by
        ext B
        exact (monomial_union p I J B).symm
      rw [h_prod]
      apply monomial_mem_degSubmodule
      exact (card_union_le I J).trans (add_le_add hI hJ)
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add g1 g2 _ _ ih1 ih2 =>
      rw [mul_add]
      exact Submodule.add_mem _ ih1 ih2
    | smul c g1 _ ih =>
      have h_smul : (monomial p I : Finset α → ZMod p) * (c • g1) = c • (monomial p I * g1) := by
        ext B
        simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [h_smul]
      exact Submodule.smul_mem _ c ih
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add f1 f2 _ _ ih1 ih2 =>
    rw [add_mul]
    exact Submodule.add_mem _ ih1 ih2
  | smul c f1 _ ih =>
    have h_smul : (c • f1) * g = c • (f1 * g) := by
      ext B
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h_smul]
    exact Submodule.smul_mem _ c ih

lemma prod_card_inter_sub_mem_degSubmodule (p : ℕ) (A : Finset α) (T : Finset (ZMod p)) :
    (fun B ↦ ∏ l ∈ T, (((A ∩ B).card : ZMod p) - l) : Finset α → ZMod p) ∈ degSubmodule (α := α) p T.card := by
  induction T using Finset.induction_on with
  | empty =>
    have h_one : (fun B ↦ ∏ l ∈ (∅ : Finset (ZMod p)), (((A ∩ B).card : ZMod p) - l) : Finset α → ZMod p) = 1 := by
      ext B
      simp
    rw [card_empty, h_one]
    exact one_mem_degSubmodule p 0
  | @insert l T' hl ih =>
    rw [card_insert_of_notMem hl]
    have h_prod : (fun B ↦ ∏ x ∈ insert l T', (((A ∩ B).card : ZMod p) - x) : Finset α → ZMod p) =
        (fun B ↦ ((A ∩ B).card : ZMod p) - l) * (fun B ↦ ∏ x ∈ T', (((A ∩ B).card : ZMod p) - x)) := by
      ext B
      simp [prod_insert hl]
    rw [h_prod]
    have h_step := mul_mem_degSubmodule p (card_inter_sub_const_mem_degSubmodule p A l) ih
    rw [add_comm]
    exact h_step


lemma evalPoly_mem_degSubmodule (p : ℕ) (L : Finset (ZMod p)) (A : Finset α) :
    (evalPoly p L A : Finset α → ZMod p) ∈ degSubmodule (α := α) p L.card :=
  prod_card_inter_sub_mem_degSubmodule p A L

-- ============================================================================
-- Section 5: Dimension Bounds and Subsets Counting
-- ============================================================================

lemma card_filter_le_card_subsets (s : ℕ) :
    (Finset.univ.filter (fun (I : Finset α) ↦ I.card ≤ s)).card =
      ∑ i ∈ Finset.range (s + 1), Nat.choose (Fintype.card α) i := by
  have h_eq : (Finset.univ.filter (fun (I : Finset α) ↦ I.card ≤ s)) =
      (Finset.range (s + 1)).biUnion (fun i ↦ powersetCard i (Finset.univ : Finset α)) := by
    ext I
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range, mem_powersetCard, subset_univ]
    constructor
    · intro hI
      exact ⟨I.card, Nat.lt_succ_of_le hI, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact Nat.le_of_lt_succ hi
  rw [h_eq, card_biUnion]
  · apply sum_congr rfl
    intro i _
    rw [card_powersetCard, card_univ]
  · intro i _ j _ hij
    dsimp [Function.onFun]
    rw [Finset.disjoint_iff_ne]
    rintro I hI J hJ rfl
    rw [mem_powersetCard] at hI hJ
    exact hij (hI.2.symm.trans hJ.2)

lemma fintype_card_subtype_le_card (s : ℕ) :
    Fintype.card {I : Finset α // I.card ≤ s} =
      ∑ i ∈ Finset.range (s + 1), Nat.choose (Fintype.card α) i := by
  rw [Fintype.card_subtype, card_filter_le_card_subsets]

lemma finrank_degSubmodule_le (p : ℕ) [Fact (Nat.Prime p)] (s : ℕ) :
    Module.finrank (ZMod p) (degSubmodule (α := α) p s) ≤
      ∑ i ∈ Finset.range (s + 1), Nat.choose (Fintype.card α) i := by
  have h_le := finrank_range_le_card (R := ZMod p) (fun (I : {I : Finset α // I.card ≤ s}) ↦ (monomial p I.1 : Finset α → ZMod p))
  rw [fintype_card_subtype_le_card] at h_le
  exact h_le

-- ============================================================================
-- Section 6: Frankl–Wilson Theorem
-- ============================================================================

/-- General Frankl–Wilson Theorem (1981):
    |F| ≤ ∑_{i=0}^s Nat.choose n i where s = |L|. -/
theorem frankl_wilson_general (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L) :
    fam.F.card ≤ ∑ i ∈ Finset.range (L.card + 1), Nat.choose (Fintype.card α) i := by
  let W : Submodule (ZMod p) (Finset α → ZMod p) := degSubmodule p L.card
  let f : fam.F → W := fun A ↦ ⟨evalPoly p L A.1, evalPoly_mem_degSubmodule p L A.1⟩
  have h_comp : (fun (A : fam.F) ↦ (evalPoly p L A.1 : Finset α → ZMod p)) = (fun A ↦ (f A : Finset α → ZMod p)) := rfl
  have h_li_orig := evalPoly_linearIndependent p L fam
  rw [h_comp] at h_li_orig
  have h_li : LinearIndependent (ZMod p) f := by
    exact LinearIndependent.of_comp W.subtype h_li_orig
  have h_card_le := LinearIndependent.fintype_card_le_finrank h_li
  rw [Fintype.card_coe] at h_card_le
  have h_dim_le := finrank_degSubmodule_le (α := α) p L.card
  exact h_card_le.trans h_dim_le



-- ============================================================================
-- Section 7: Uniform Frankl–Wilson Theorem
-- ============================================================================

/-- Submodule of ({B : Finset α // B.card = k} → ZMod p) spanned by monomials of size exactly `s`. -/
def exactSubmodule (p : ℕ) (k : ℕ) (s : ℕ) :
    Submodule (ZMod p) ({B : Finset α // B.card = k} → ZMod p) :=
  Submodule.span (ZMod p)
    (Set.range (fun (I : {I : Finset α // I.card = s}) ↦
      (fun (B : {B : Finset α // B.card = k}) ↦ monomial p I.1 B.1)))

lemma fintype_card_subtype_eq_card (s : ℕ) :
    Fintype.card {I : Finset α // I.card = s} = Nat.choose (Fintype.card α) s := by
  rw [Fintype.card_subtype]
  have h_eq : (Finset.univ.filter (fun (I : Finset α) ↦ I.card = s)) = powersetCard s (Finset.univ : Finset α) := by
    ext I
    simp [mem_powersetCard]
  rw [h_eq, card_powersetCard, card_univ]

lemma finrank_exactSubmodule_le (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ) (s : ℕ) :
    Module.finrank (ZMod p) (exactSubmodule (α := α) p k s) ≤ Nat.choose (Fintype.card α) s := by
  have h_le := finrank_range_le_card (R := ZMod p)
    (fun (I : {I : Finset α // I.card = s}) ↦
      (fun (B : {B : Finset α // B.card = k}) ↦ monomial p I.1 B.1))
  rw [fintype_card_subtype_eq_card] at h_le
  exact h_le

lemma monomial_sum_univ_sub (p : ℕ) (k : ℕ) (J : Finset α) (B : {B : Finset α // B.card = k}) :
    ((k : ZMod p) - (J.card : ZMod p)) * monomial p J B.1 =
      ∑ i ∈ Finset.univ \ J, monomial p (insert i J) B.1 := by
  have h_tot : (∑ i ∈ (Finset.univ : Finset α), monomial p {i} B.1) = (k : ZMod p) := by
    rw [sum_monomial_singleton]
    have h_inter : (Finset.univ ∩ B.1) = B.1 := by
      ext x
      simp
    rw [h_inter, B.2]
  have h_split : (∑ i ∈ (Finset.univ : Finset α), monomial p {i} B.1 * monomial p J B.1) =
      (∑ i ∈ J, monomial p {i} B.1 * monomial p J B.1) +
        ∑ i ∈ Finset.univ \ J, monomial p {i} B.1 * monomial p J B.1 := by
    have h_disj : Disjoint J (Finset.univ \ J) := disjoint_sdiff
    have h_union : J ∪ (Finset.univ \ J) = Finset.univ := union_sdiff_of_subset (subset_univ J)
    nth_rw 1 [← h_union]
    rw [sum_union h_disj]
  have h_lhs : (∑ i ∈ (Finset.univ : Finset α), monomial p {i} B.1 * monomial p J B.1) =
      (k : ZMod p) * monomial p J B.1 := by
    rw [← sum_mul, h_tot]
  have h_J_part : (∑ i ∈ J, monomial p {i} B.1 * monomial p J B.1) = (J.card : ZMod p) * monomial p J B.1 := by
    have h_term : ∀ i ∈ J, monomial p {i} B.1 * monomial p J B.1 = monomial p J B.1 := by
      intro i hi
      rw [← monomial_union]
      have h_u : {i} ∪ J = J := by
        ext x
        simp only [mem_union, mem_singleton]
        constructor
        · rintro (rfl | hx)
          · exact hi
          · exact hx
        · intro hx
          exact Or.inr hx
      rw [h_u]
    rw [sum_congr rfl h_term, sum_const, nsmul_eq_mul]
  have h_diff_part : (∑ i ∈ Finset.univ \ J, monomial p {i} B.1 * monomial p J B.1) =
      ∑ i ∈ Finset.univ \ J, monomial p (insert i J) B.1 := by
    apply sum_congr rfl
    intro i _
    rw [← monomial_union]
    have h_u : {i} ∪ J = insert i J := by
      ext x
      simp
    rw [h_u]
  rw [h_lhs, h_J_part, h_diff_part] at h_split
  linear_combination h_split


lemma monomial_mem_exactSubmodule_aux (p : ℕ) [Fact (Nat.Prime p)] (k s : ℕ)
    (hk_diff : ∀ j < s, (k : ZMod p) ≠ (j : ZMod p)) :
    ∀ (m : ℕ) (J : Finset α), J.card ≤ s → s - J.card = m →
      (fun (B : {B : Finset α // B.card = k}) ↦ monomial p J B.1) ∈ exactSubmodule (α := α) p k s
  | 0, J, hJs, hm => by
    have hJ_eq : J.card = s := by omega
    apply Submodule.subset_span
    exact ⟨⟨J, hJ_eq⟩, rfl⟩
  | m + 1, J, hJs, hm => by
    have h_lt : J.card < s := by omega
    have h_diff_nz : (k : ZMod p) - (J.card : ZMod p) ≠ 0 := by
      intro heq
      have h_eq_k : (k : ZMod p) = (J.card : ZMod p) := sub_eq_zero.mp heq
      exact hk_diff J.card h_lt h_eq_k
    have h_step : ∀ i ∈ Finset.univ \ J,
        (fun (B : {B : Finset α // B.card = k}) ↦ monomial p (insert i J) B.1) ∈ exactSubmodule (α := α) p k s := by
      intro i hi
      have hi_not : i ∉ J := (mem_sdiff.mp hi).2
      have h_card_ins : (insert i J).card = J.card + 1 := card_insert_of_notMem hi_not
      have h_le_ins : (insert i J).card ≤ s := by omega
      have h_m_ins : s - (insert i J).card = m := by omega
      exact monomial_mem_exactSubmodule_aux p k s hk_diff m (insert i J) h_le_ins h_m_ins
    have h_sum_mem : (∑ i ∈ Finset.univ \ J, (fun (B : {B : Finset α // B.card = k}) ↦ monomial p (insert i J) B.1)) ∈
        exactSubmodule (α := α) p k s := by
      apply Submodule.sum_mem
      exact h_step
    have h_id : ((k : ZMod p) - (J.card : ZMod p)) • (fun (B : {B : Finset α // B.card = k}) ↦ monomial p J B.1) =
        ∑ i ∈ Finset.univ \ J, (fun (B : {B : Finset α // B.card = k}) ↦ monomial p (insert i J) B.1) := by
      ext B
      simp only [Pi.smul_apply, smul_eq_mul, sum_apply]
      exact monomial_sum_univ_sub p k J B
    have h_inv : (fun (B : {B : Finset α // B.card = k}) ↦ monomial p J B.1) =
        ((k : ZMod p) - (J.card : ZMod p))⁻¹ •
          ∑ i ∈ Finset.univ \ J, (fun (B : {B : Finset α // B.card = k}) ↦ monomial p (insert i J) B.1) := by
      rw [← h_id, smul_smul, inv_mul_cancel₀ h_diff_nz, one_smul]
    rw [h_inv]
    exact Submodule.smul_mem _ _ h_sum_mem

lemma monomial_mem_exactSubmodule (p : ℕ) [Fact (Nat.Prime p)] (k s : ℕ)
    (hk_diff : ∀ j < s, (k : ZMod p) ≠ (j : ZMod p)) {J : Finset α} (hJs : J.card ≤ s) :
    (fun (B : {B : Finset α // B.card = k}) ↦ monomial p J B.1) ∈ exactSubmodule (α := α) p k s :=
  monomial_mem_exactSubmodule_aux p k s hk_diff (s - J.card) J hJs rfl

lemma restrict_degSubmodule_mem_exactSubmodule (p : ℕ) [Fact (Nat.Prime p)] (k s : ℕ)
    (hk_diff : ∀ j < s, (k : ZMod p) ≠ (j : ZMod p)) {f : Finset α → ZMod p}
    (hf : f ∈ degSubmodule (α := α) p s) :
    (fun (B : {B : Finset α // B.card = k}) ↦ f B.1) ∈ exactSubmodule (α := α) p k s := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨I, hI⟩, rfl⟩ := hg
    exact monomial_mem_exactSubmodule p k s hk_diff hI
  | zero =>
    have h_zero : (fun (B : {B : Finset α // B.card = k}) ↦ (0 : Finset α → ZMod p) B.1) = 0 := rfl
    rw [h_zero]
    exact Submodule.zero_mem _
  | add g1 g2 _ _ ih1 ih2 =>
    have h_add : (fun (B : {B : Finset α // B.card = k}) ↦ (g1 + g2) B.1) =
        (fun B ↦ g1 B.1) + (fun B ↦ g2 B.1) := rfl
    rw [h_add]
    exact Submodule.add_mem _ ih1 ih2
  | smul c g1 _ ih =>
    have h_smul : (fun (B : {B : Finset α // B.card = k}) ↦ (c • g1) B.1) =
        c • (fun B ↦ g1 B.1) := rfl
    rw [h_smul]
    exact Submodule.smul_mem _ c ih

/-- Uniform Cardinality Frankl–Wilson Theorem (1981):
    If all subsets in F have equal size k with (k : ZMod p) ∉ L, and k mod p ≠ j mod p for all j < |L|,
    then |F| ≤ Nat.choose n s. -/
theorem frankl_wilson_uniform (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L)
    (k : ℕ) (h_uniform : ∀ A ∈ fam.F, A.card = k)
    (hk_diff : ∀ j < L.card, (k : ZMod p) ≠ (j : ZMod p)) :
    fam.F.card ≤ Nat.choose (Fintype.card α) L.card := by
  let S_k := {B : Finset α // B.card = k}
  let W_ex := exactSubmodule (α := α) p k L.card
  have h_mem : ∀ A ∈ fam.F, (fun (B : S_k) ↦ evalPoly p L A B.1) ∈ W_ex := by
    intro A _
    exact restrict_degSubmodule_mem_exactSubmodule p k L.card hk_diff (evalPoly_mem_degSubmodule p L A)
  let f : fam.F → W_ex := fun A ↦ ⟨fun (B : S_k) ↦ evalPoly p L A.1 B.1, h_mem A.1 A.2⟩
  have h_li_ambient : LinearIndependent (ZMod p) (fun (A : fam.F) ↦ (fun (B : S_k) ↦ evalPoly p L A.1 B.1)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have h_eval : (∑ A ∈ s, g A • (fun (B : S_k) ↦ evalPoly p L A.1 B.1)) ⟨i.1, h_uniform i.1 i.2⟩ = 0 := by
      rw [hg]
      rfl
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h_eval
    have h_single : (∑ A ∈ s, g A * evalPoly p L A.1 i.1) = g i * evalPoly p L i.1 i.1 := by
      apply sum_eq_single i
      · intro A _ hAi
        have hne : (A : Finset α) ≠ i.1 := by
          intro heq
          exact hAi (Subtype.ext heq)
        rw [evalPoly_other_eq_zero p L fam A.1 i.1 A.2 i.2 hne, mul_zero]
      · intro h_not_mem
        exact False.elim (h_not_mem hi)
    rw [h_single] at h_eval
    have h_nz := evalPoly_self_ne_zero p L fam i.1 i.2
    cases mul_eq_zero.mp h_eval with
    | inl hg_zero => exact hg_zero
    | inr h_zero => exact False.elim (h_nz h_zero)
  have h_comp : (fun (A : fam.F) ↦ (fun (B : S_k) ↦ evalPoly p L A.1 B.1)) = (fun A ↦ (f A : S_k → ZMod p)) := rfl
  rw [h_comp] at h_li_ambient
  have h_li : LinearIndependent (ZMod p) f := LinearIndependent.of_comp W_ex.subtype h_li_ambient
  have h_card_le := LinearIndependent.fintype_card_le_finrank h_li
  rw [Fintype.card_coe] at h_card_le
  have h_dim_le := finrank_exactSubmodule_le (α := α) p k L.card
  exact h_card_le.trans h_dim_le