import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Common
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination

/-!
# Radon's Lemma and Helly's Theorem (Freek Wiedijk #99)

This module formalizes **Radon's Lemma (Radon's Theorem)** (J. Radon, 1921)
and **Helly's Theorem on Convex Sets** (E. Helly, 1923) completely from
**first principles** without using Mathlib's pre-packaged Radon/Helly modules.

## Main Declarations

1. `RadonHelly.radons_theorem`:
   Any set $S$ of $d + 2$ points in $\mathbb{R}^d$ can be partitioned into two disjoint subsets
   $A$ and $B$ whose convex hulls intersect:
   $$A \cap B = \emptyset, \quad A \cup B = S, \quad \operatorname{conv}(A) \cap \operatorname{conv}(B) \ne \emptyset$$

2. `RadonHelly.hellys_theorem`:
   Let $C_i$ ($i \in \iota$) be a finite family of convex subsets in $\mathbb{R}^d$.
   If every subfamily of size at most $d + 1$ has non-empty intersection, then the entire family
   has non-empty intersection:
   $$\bigcap_{i \in \iota} C_i \ne \emptyset$$

## References
* J. Radon (1921), *Mengen konvexer Körper, die einen gemeinsamen Punkt enthalten*, Math. Ann., 83(1-2):113–115.
* E. Helly (1923), *Über Mengen konvexer Körper mit gemeinschaftlichen Punkten*, Jahresber. Deutsch. Math.-Verein., 32:175–176.
* F. Wiedijk (2008), *Formalizing 100 Theorems*, #99.
-/

set_option linter.deprecated false

namespace RadonHelly

open Finset

variable {d : ℕ}

/-- Coordinate sum as a linear map. -/
def sumCoord (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun c := ∑ i, c i
  map_add' _ _ := sum_add_distrib
  map_smul' _ _ := by simp [mul_sum]

/-- Weighted sum of points as a linear map. -/
def sumPoints (n : ℕ) (v : Fin n → (Fin d → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun c := ∑ i, c i • v i
  map_add' _ _ := by simp [sum_add_distrib, add_smul]
  map_smul' _ _ := by simp [smul_sum, mul_smul]

/-- The combined linear map for Radon's lemma. -/
def radonMap (v : Fin (d + 2) → (Fin d → ℝ)) :
    (Fin (d + 2) → ℝ) →ₗ[ℝ] (ℝ × (Fin d → ℝ)) :=
  (sumCoord (d + 2)).prod (sumPoints (d + 2) v)

lemma exists_nonzero_radon_coeff (v : Fin (d + 2) → (Fin d → ℝ)) :
    ∃ c : Fin (d + 2) → ℝ, c ≠ 0 ∧ (∑ i, c i = 0) ∧ (∑ i, c i • v i = 0) := by
  have h_not_inj : ¬ Function.Injective (radonMap v) := fun h ↦ by
    have := LinearMap.finrank_le_finrank_of_injective h
    simp [Module.finrank_prod] at this; omega
  obtain ⟨c, hc_mem, hc_ne⟩ := (Submodule.ne_bot_iff _).1 (mt LinearMap.ker_eq_bot.mp h_not_inj)
  exact ⟨c, hc_ne, (Prod.mk_eq_zero.mp hc_mem).1, (Prod.mk_eq_zero.mp hc_mem).2⟩

theorem radons_theorem (S : Finset (Fin d → ℝ)) (hS : S.card = d + 2) :
    ∃ A B : Finset (Fin d → ℝ), A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ A ∪ B = S ∧
      (convexHull ℝ (A : Set (Fin d → ℝ)) ∩ convexHull ℝ (B : Set (Fin d → ℝ))).Nonempty := by
  classical
  let e : Fin (d + 2) ≃ S := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hS])).symm
  let v : Fin (d + 2) → (Fin d → ℝ) := fun i ↦ (e i : Fin d → ℝ)
  obtain ⟨c, hc_ne, hc_sum, hc_sum_v⟩ := exists_nonzero_radon_coeff v
  let I_pos := Finset.univ.filter (fun i ↦ 0 < c i)
  let I_neg := Finset.univ.filter (fun i ↦ c i ≤ 0)
  have h_disj_I : Disjoint I_pos I_neg := disjoint_filter.mpr fun _ _ h => not_le.mpr h
  have h_union_I : I_pos ∪ I_neg = univ := by
    ext x; simp only [I_pos, I_neg, mem_union, mem_filter, mem_univ, true_and]; exact iff_true_intro (lt_or_ge 0 (c x))
  have h_sum_split : (∑ i ∈ I_pos, c i) + (∑ i ∈ I_neg, c i) = 0 := by rw [← sum_union h_disj_I, h_union_I, hc_sum]
  have h_sum_v_split : (∑ i ∈ I_pos, c i • v i) + (∑ i ∈ I_neg, c i • v i) = 0 := by rw [← sum_union h_disj_I, h_union_I, hc_sum_v]
  have ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by contrapose! hc_ne; ext i; exact hc_ne i
  have h_pos_sum : 0 < ∑ i ∈ I_pos, c i := by
    rcases lt_or_gt_of_ne hi₀ with h_neg | h_pos
    · have hi₀_mem : i₀ ∈ I_neg := mem_filter.mpr ⟨mem_univ _, le_of_lt h_neg⟩
      have h_sub : ∑ i ∈ I_neg \ {i₀}, c i ≤ 0 := sum_nonpos fun i hi => (mem_filter.mp (mem_sdiff.mp hi).1).2
      have h_dec : ∑ i ∈ I_neg, c i = c i₀ + ∑ i ∈ I_neg \ {i₀}, c i := by
        rw [← add_sum_erase _ _ hi₀_mem, sdiff_singleton_eq_erase]
      linarith
    · have hi₀_mem : i₀ ∈ I_pos := mem_filter.mpr ⟨mem_univ _, h_pos⟩
      have h_ge : c i₀ ≤ ∑ i ∈ I_pos, c i := single_le_sum (fun i hi => le_of_lt (mem_filter.mp hi).2) hi₀_mem
      linarith
  let C := ∑ i ∈ I_pos, c i
  have hC_pos : 0 < C := h_pos_sum
  have hC_neg_sum : ∑ i ∈ I_neg, -c i = C := by rw [sum_neg_distrib]; linarith [h_sum_split]
  have hC_neg_pos : 0 < ∑ i ∈ I_neg, -c i := by rwa [hC_neg_sum]
  let A : Finset (Fin d → ℝ) := I_pos.image v
  let B : Finset (Fin d → ℝ) := I_neg.image v
  have hA_sub : A ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact (e i).2
  have hB_sub : B ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact (e i).2
  have h_disj : Disjoint A B := by
    rw [Finset.disjoint_iff_ne]
    rintro x hx y hy rfl
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, hj, heq⟩
    have heq_s : e i = e j := Subtype.ext heq.symm
    have hij : i = j := e.injective heq_s
    subst hij
    have hi_pos : 0 < c i := (Finset.mem_filter.mp hi).2
    have hi_neg : c i ≤ 0 := (Finset.mem_filter.mp hj).2
    linarith
  have h_union : A ∪ B = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hA | hB
      · exact hA_sub hA
      · exact hB_sub hB
    · intro hx
      let s_elem : S := ⟨x, hx⟩
      let i : Fin (d + 2) := e.symm s_elem
      have hi_v : v i = x := by
        dsimp [v, i, s_elem]
        rw [Equiv.apply_symm_apply]
      by_cases hc_i : 0 < c i
      · apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc_i⟩, hi_v⟩
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        have : c i ≤ 0 := by linarith
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, this⟩, hi_v⟩
  have h_pts_eq : ∑ i ∈ I_pos, c i • v i = ∑ i ∈ I_neg, (-c i) • v i := by
    calc ∑ i ∈ I_pos, c i • v i = - ∑ i ∈ I_neg, c i • v i := by
           rw [← add_eq_zero_iff_eq_neg]
           exact h_sum_v_split
         _ = ∑ i ∈ I_neg, (-c i) • v i := by
           simp_rw [neg_smul, Finset.sum_neg_distrib]
  let p : Fin d → ℝ := I_pos.centerMass c v
  have hp_A : p ∈ convexHull ℝ (A : Set (Fin d → ℝ)) := by
    apply Finset.centerMass_mem_convexHull I_pos (fun i hi ↦ le_of_lt (Finset.mem_filter.mp hi).2) hC_pos
    intro i hi
    exact Finset.mem_image_of_mem v hi
  have hp_B : p ∈ convexHull ℝ (B : Set (Fin d → ℝ)) := by
    have hp_eq : p = I_neg.centerMass (fun i ↦ -c i) v := by
      dsimp [p, Finset.centerMass, C]
      rw [hC_neg_sum, h_pts_eq]
    rw [hp_eq]
    apply Finset.centerMass_mem_convexHull I_neg (fun i hi ↦ neg_nonneg.mpr (Finset.mem_filter.mp hi).2) hC_neg_pos
    intro i hi
    exact Finset.mem_image_of_mem v hi
  refine ⟨A, B, hA_sub, hB_sub, h_disj, h_union, ⟨p, hp_A, hp_B⟩⟩

/-- Helper lemma for Helly's theorem: induction on the size of the finset `S`. -/
lemma hellys_theorem_card {ι : Type*} [DecidableEq ι] (n : ℕ)
    (C : ι → Set (Fin d → ℝ)) (h_convex : ∀ i, Convex ℝ (C i))
    (S : Finset ι) (hS : S.card = n)
    (h_inter : ∀ J ⊆ S, J.card ≤ d + 1 → (⋂ i ∈ J, C i).Nonempty) :
    (⋂ i ∈ S, C i).Nonempty := by
  induction' n using Nat.strong_induction_on with n ih generalizing ι C S
  by_cases h_base : n ≤ d + 1
  · exact h_inter S (Subset.refl S) (by omega)
  · by_cases h_radon : n = d + 2
    · have hj_inter_all : ∀ j ∈ S, (⋂ i ∈ S.erase j, C i).Nonempty := by
        intro j hj
        have hj_sub : S.erase j ⊆ S := Finset.erase_subset j S
        have hj_card : (S.erase j).card = d + 1 := by
          rw [Finset.card_erase_of_mem hj, hS, h_radon]
          rfl
        have hj_inter : ∀ J ⊆ S.erase j, J.card ≤ d + 1 → (⋂ i ∈ J, C i).Nonempty :=
          fun J hJ hJ_card ↦ h_inter J (hJ.trans hj_sub) hJ_card
        exact ih (d + 1) (by omega) C h_convex (S.erase j) hj_card hj_inter
      choose p hp using fun (j : S) ↦ hj_inter_all j.1 j.2
      by_cases hp_inj : Function.Injective p
      · let P_pts : Finset (Fin d → ℝ) := Finset.univ.image p
        have h_card_pts : P_pts.card = d + 2 := by
          rw [Finset.card_image_of_injective Finset.univ hp_inj, Finset.card_univ, Fintype.card_coe, hS, h_radon]
        obtain ⟨A, B, hA_sub, hB_sub, h_disj, h_union, ⟨x, hx_A, hx_B⟩⟩ :=
          radons_theorem P_pts h_card_pts
        refine ⟨x, ?_⟩
        rw [Set.mem_iInter₂]
        intro k hk
        let pk : Fin d → ℝ := p ⟨k, hk⟩
        have hpk_mem : pk ∈ P_pts := Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩
        have hpk_union : pk ∈ A ∪ B := by rw [h_union]; exact hpk_mem
        by_cases hpk_A : pk ∈ A
        · have hpk_nB : pk ∉ B := by
            intro h_in_B
            exact (Finset.disjoint_iff_ne.mp h_disj) pk hpk_A pk h_in_B rfl
          have hB_subset_Ck : (B : Set (Fin d → ℝ)) ⊆ C k := by
            intro y hy
            rcases Finset.mem_image.mp (hB_sub hy) with ⟨⟨j, hj⟩, _, rfl⟩
            have hjk : j ≠ k := by
              intro heq
              have h_eq_pk : p ⟨j, hj⟩ = pk := by
                dsimp [pk]
                congr 1
                exact Subtype.ext heq
              rw [h_eq_pk] at hy
              exact hpk_nB hy
            have hj_erase : k ∈ S.erase j := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
            exact Set.mem_iInter₂.mp (hp ⟨j, hj⟩) k hj_erase
          have h_hull_B : convexHull ℝ (B : Set (Fin d → ℝ)) ⊆ C k :=
            convexHull_min hB_subset_Ck (h_convex k)
          exact h_hull_B hx_B
        · have hA_subset_Ck : (A : Set (Fin d → ℝ)) ⊆ C k := by
            intro y hy
            rcases Finset.mem_image.mp (hA_sub hy) with ⟨⟨j, hj⟩, _, rfl⟩
            have hjk : j ≠ k := by
              intro heq
              have h_eq_pk : p ⟨j, hj⟩ = pk := by
                dsimp [pk]
                congr 1
                exact Subtype.ext heq
              rw [h_eq_pk] at hy
              exact hpk_A hy
            have hj_erase : k ∈ S.erase j := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
            exact Set.mem_iInter₂.mp (hp ⟨j, hj⟩) k hj_erase
          have h_hull_A : convexHull ℝ (A : Set (Fin d → ℝ)) ⊆ C k :=
            convexHull_min hA_subset_Ck (h_convex k)
          exact h_hull_A hx_A
      · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hp_eq, hab⟩ : ∃ x y : S, p x = p y ∧ x ≠ y := by
          contrapose! hp_inj
          intro x y heq
          exact hp_inj x y heq
        have hab_ne : a ≠ b := fun h ↦ hab (Subtype.ext h)
        refine ⟨p ⟨a, ha⟩, ?_⟩
        rw [Set.mem_iInter₂]
        intro k hk
        by_cases hka : k = a
        · subst hka
          have hkb : k ≠ b := hab_ne
          have h_mem_erase : k ∈ S.erase b := Finset.mem_erase.mpr ⟨hkb, hk⟩
          have hpb := Set.mem_iInter₂.mp (hp ⟨b, hb⟩) k h_mem_erase
          rw [hp_eq]
          exact hpb
        · have h_mem_erase : k ∈ S.erase a := Finset.mem_erase.mpr ⟨hka, hk⟩
          exact Set.mem_iInter₂.mp (hp ⟨a, ha⟩) k h_mem_erase
    · have hn_gt : d + 2 < n := by omega
      have hn_ge2 : 1 < S.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hn_ge2
      let S' := S.erase b
      have hS'_card : S'.card = n - 1 := by
        rw [Finset.card_erase_of_mem hb, hS]
      have ha_in_S' : a ∈ S' := Finset.mem_erase.mpr ⟨hab, ha⟩
      let C' : ι → Set (Fin d → ℝ) := fun i ↦ if i = a then C a ∩ C b else C i
      have h_convex' : ∀ i, Convex ℝ (C' i) := by
        intro i
        dsimp [C']
        split_ifs
        · exact (h_convex a).inter (h_convex b)
        · exact h_convex i
      have h_inter' : ∀ J ⊆ S', J.card ≤ d + 1 → (⋂ i ∈ J, C' i).Nonempty := by
        intro J hJ hJ_card
        by_cases haJ : a ∈ J
        · let J_orig := insert b J
          have hb_not_J : b ∉ J := fun h ↦ (Finset.mem_erase.mp (hJ h)).1 rfl
          have hJ_orig_card : J_orig.card ≤ d + 2 := by
            rw [Finset.card_insert_of_notMem hb_not_J]
            omega
          have hJ_orig_lt : J_orig.card < n := by omega
          have hJ_orig_sub : J_orig ⊆ S := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx_J
            · exact hb
            · exact (Finset.erase_subset b S) (hJ hx_J)
          have hJ_orig_inter : ∀ K ⊆ J_orig, K.card ≤ d + 1 → (⋂ i ∈ K, C i).Nonempty := by
            intro K hK hK_card
            exact h_inter K (hK.trans hJ_orig_sub) hK_card
          have h_nonempty_J_orig :=
            ih J_orig.card hJ_orig_lt C h_convex J_orig rfl hJ_orig_inter
          obtain ⟨y, hy⟩ := h_nonempty_J_orig
          refine ⟨y, ?_⟩
          rw [Set.mem_iInter₂]
          intro i hi
          dsimp [C']
          by_cases hia : i = a
          · rw [if_pos hia]
            have h_a_in : a ∈ J_orig := Finset.mem_insert_of_mem haJ
            have h_b_in : b ∈ J_orig := Finset.mem_insert_self b J
            exact ⟨Set.mem_iInter₂.mp hy a h_a_in, Set.mem_iInter₂.mp hy b h_b_in⟩
          · rw [if_neg hia]
            have hi_in : i ∈ J_orig := Finset.mem_insert_of_mem hi
            exact Set.mem_iInter₂.mp hy i hi_in
        · have hJ_sub_S : J ⊆ S := hJ.trans (Finset.erase_subset b S)
          obtain ⟨y, hy⟩ := h_inter J hJ_sub_S hJ_card
          refine ⟨y, ?_⟩
          rw [Set.mem_iInter₂]
          intro i hi
          have hia : i ≠ a := fun h ↦ haJ (h ▸ hi)
          dsimp [C']
          rw [if_neg hia]
          exact Set.mem_iInter₂.mp hy i hi
      have h_ih_S' := ih (n - 1) (by omega) C' h_convex' S' hS'_card h_inter'
      obtain ⟨z, hz⟩ := h_ih_S'
      refine ⟨z, ?_⟩
      rw [Set.mem_iInter₂]
      intro i hi
      by_cases hib : i = b
      · subst hib
        have h_za := Set.mem_iInter₂.mp hz a ha_in_S'
        dsimp [C'] at h_za
        rw [if_pos rfl] at h_za
        exact h_za.2
      · have hi_S' : i ∈ S' := Finset.mem_erase.mpr ⟨hib, hi⟩
        have h_zi := Set.mem_iInter₂.mp hz i hi_S'
        dsimp [C'] at h_zi
        by_cases hia : i = a
        · rw [if_pos hia] at h_zi
          exact hia ▸ h_zi.1
        · rw [if_neg hia] at h_zi
          exact h_zi

/-- **Helly's Theorem for Finite Families of Convex Sets (1923, Freek Wiedijk #99):**
If `C` is a finite family of convex subsets in `Fin d → ℝ` such that every subfamily of size
at most `d + 1` (`J.card ≤ d + 1`) has non-empty intersection, then the entire family has
non-empty intersection.

### Small-Family Scope and Equivalence
- **Boundary / Small Families (`|ι| ≤ d + 1`)**: For families with `|ι| ≤ d + 1`, choosing
  `J = Finset.univ` satisfies `J.card ≤ d + 1`, so the hypothesis directly entails that the entire
  family has non-empty intersection. The `≤ d + 1` hypothesis avoids the vacuous-truth failure of
  the exact-size `= d + 1` condition when `|ι| ≤ d`.
- **Large Families (`|ι| > d + 1`)**: When `|ι| > d + 1`, any subfamily of size `≤ d + 1` can be
  extended to a subfamily of size `d + 1`, so the `≤ d + 1` condition is equivalent to the classical
  statement requiring every `(d + 1)`-element subfamily to intersect. -/
theorem hellys_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → Set (Fin d → ℝ))
    (h_convex : ∀ i : ι, Convex ℝ (C i))
    (h_inter : ∀ J : Finset ι, J.card ≤ d + 1 → (⋂ i ∈ J, C i).Nonempty) :
    (⋂ i : ι, C i).Nonempty := by
  have h_univ : (⋂ i ∈ (Finset.univ : Finset ι), C i).Nonempty :=
    hellys_theorem_card (Finset.univ.card) C h_convex Finset.univ rfl (fun J _ hJ ↦ h_inter J hJ)
  obtain ⟨x, hx⟩ := h_univ
  refine ⟨x, ?_⟩
  rw [Set.mem_iInter]
  intro i
  exact Set.mem_iInter₂.mp hx i (Finset.mem_univ i)

#print axioms radons_theorem
#print axioms hellys_theorem

end RadonHelly

