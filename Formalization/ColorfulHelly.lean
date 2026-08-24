import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Formalization.RadonHelly

/-!
# Lovász's Colorful Helly Theorem (1974; first published proof 1982)

**Theorem statement (Lovász; first published in Bárány 1982, Theorem 3.1):**
Let $\mathcal{F}_0, \mathcal{F}_1, \dots, \mathcal{F}_d$ be $d+1$ finite families of convex sets
in $\mathbb{R}^d$. If every colorful transversal (i.e. every selection of one set
$S_i \in \mathcal{F}_i$ for each $i \in \{0, \dots, d\}$) has a non-empty intersection
$\bigcap_{i=0}^d S_i \ne \emptyset$, then at least one family $\mathcal{F}_j$ has a non-empty
global intersection:
$$\exists j \in \{0, \dots, d\}, \quad \bigcap_{S \in \mathcal{F}_j} S \ne \emptyset.$$

### Proof strategy:
We first replace every set by the convex hull of the finite pool of transversal witnesses lying
in it.  These replacements are compact convex subsets of the original sets and preserve every
colorful intersection.  Among all colorful choices, we maximize the minimum squared Euclidean
length on the intersection.  Helly's theorem, applied after adjoining the strict lower sublevel
set, shows that at most $d$ chosen sets determine this minimum.  Replacing the omitted color and
using strict convexity then forces the extremal point to lie in every set of that color.

### Source and formalization scope

Lovász discovered the colorful Helly theorem in 1974; Bárány supplied its first published proof
and credited Lovász's private communication.  Bárány states the result for compact convex sets.
Here the families are finite but their members need not be compact: the proof first replaces them
by compact convex hulls of finitely many colorful-transversal witnesses.  The resulting proof is
therefore not a line-by-line transcription of Bárány's convex-function argument.

* I. Bárány, *A generalization of Carathéodory's theorem*, Discrete Mathematics 40 (1982),
  141–152, Theorem 3.1, p. 144; proof pp. 150–151.
  https://doi.org/10.1016/0012-365X(82)90115-7
-/

open BigOperators

/-- A Colorful Convex System in ℝ^d consisting of d + 1 finite families of convex sets. -/
structure ColorfulConvexSystem (d : ℕ) where
  families : Fin (d + 1) → Finset (Set (Fin d → ℝ))
  h_convex : ∀ (c : Fin (d + 1)) (S : Set (Fin d → ℝ)), S ∈ families c → Convex ℝ S

namespace ColorfulHelly

-- ============================================================================
-- Section 1: Helper Lemmas
-- ============================================================================

lemma mem_iInter_finset {α : Type*} (F : Finset (Set α)) (x : α) :
    x ∈ (⋂ S ∈ F, S) ↔ ∀ S ∈ F, x ∈ S := by
  simp only [Set.mem_iInter]

/-- The square of the Euclidean length, written in coordinates.  We use this
rather than the ambient norm on a function space (which is the sup norm). -/
private def euclideanSq (d : ℕ) (x : Fin d → ℝ) : ℝ := ∑ i, (x i) ^ 2

private lemma continuous_euclideanSq (d : ℕ) : Continuous (euclideanSq d) := by
  exact continuous_finsetSum Finset.univ (fun i _ ↦ (continuous_apply i).pow 2)

private lemma convexOn_euclideanSq (d : ℕ) : ConvexOn ℝ Set.univ (euclideanSq d) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change (∑ i, (a * x i + b * y i) ^ 2) ≤
    a * (∑ i, (x i) ^ 2) + b * (∑ i, (y i) ^ 2)
  calc
    ∑ i, (a * x i + b * y i) ^ 2 ≤ ∑ i, (a * (x i) ^ 2 + b * (y i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hn : 0 ≤ a * b * (x i - y i) ^ 2 :=
        mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x i - y i))
      nlinarith
    _ = a * ∑ i, (x i) ^ 2 + b * ∑ i, (y i) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private lemma convex_euclideanSq_lt (d : ℕ) (r : ℝ) :
    Convex ℝ {x : Fin d → ℝ | euclideanSq d x < r} := by
  simpa only [Set.mem_univ, true_and] using (convexOn_euclideanSq d).convex_lt r

private lemma euclideanSq_nonneg (d : ℕ) (x : Fin d → ℝ) : 0 ≤ euclideanSq d x := by
  exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i))

private lemma euclideanSq_eq_zero_iff (d : ℕ) (x : Fin d → ℝ) :
    euclideanSq d x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext i
    have hi : (x i) ^ 2 = 0 := by
      apply le_antisymm
      · have hle := Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
        change (∑ j, (x j) ^ 2) = 0 at h
        rw [h] at hle
        exact hle
      · exact sq_nonneg (x i)
    exact sq_eq_zero_iff.mp hi
  · rintro rfl
    simp [euclideanSq]

private lemma euclideanSq_midpoint_lt {d : ℕ} {x y : Fin d → ℝ}
    (hxy : x ≠ y) (heq : euclideanSq d x = euclideanSq d y) :
    euclideanSq d ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y) < euclideanSq d x := by
  have hdiff : 0 < euclideanSq d (x - y) := by
    exact lt_of_le_of_ne (euclideanSq_nonneg d (x - y)) (by
      intro hzero
      have : x - y = 0 := (euclideanSq_eq_zero_iff d (x - y)).mp hzero.symm
      exact hxy (sub_eq_zero.mp this))
  change (∑ i, ((2 : ℝ)⁻¹ * x i + (2 : ℝ)⁻¹ * y i) ^ 2) < ∑ i, (x i) ^ 2
  change 0 < ∑ i, (x i - y i) ^ 2 at hdiff
  change (∑ i, (x i) ^ 2) = ∑ i, (y i) ^ 2 at heq
  have hid : (∑ i, ((2 : ℝ)⁻¹ * x i + (2 : ℝ)⁻¹ * y i) ^ 2) =
      ((∑ i, (x i) ^ 2) + (∑ i, (y i) ^ 2)) / 2 -
        (∑ i, (x i - y i) ^ 2) / 4 := by
    calc
      _ = ∑ i, (((x i) ^ 2 + (y i) ^ 2) / 2 - (x i - y i) ^ 2 / 4) := by
        apply Finset.sum_congr rfl
        intro i _
        norm_num
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib]
        simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
        rw [Finset.sum_add_distrib]
  rw [hid, heq]
  linarith

/-- If any color family is empty, Colorful Helly holds vacuously. -/
lemma colorful_helly_of_empty (d : ℕ) (sys : ColorfulConvexSystem d)
    (h_empty : ∃ (c : Fin (d + 1)), sys.families c = ∅) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty := by
  rcases h_empty with ⟨c, hc⟩
  refine ⟨c, ⟨0, ?_⟩⟩
  simp only [Set.mem_iInter]
  intro S hS
  rw [hc] at hS
  cases hS

/-- Helly's Theorem for Finsets of convex sets in ℝ^d. -/
lemma finset_helly (d : ℕ) (F : Finset (Set (Fin d → ℝ)))
    (h_convex : ∀ S ∈ F, Convex ℝ S)
    (h_sub : ∀ G : Finset (Set (Fin d → ℝ)), G ⊆ F → G.card ≤ d + 1 → (⋂ S ∈ G, S).Nonempty) :
    (⋂ S ∈ F, S).Nonempty := by
  have h_conv' : ∀ (i : F), Convex ℝ (i.1) := fun i ↦ h_convex i.1 i.2
  have h_inter' : ∀ (J : Finset F), J.card ≤ d + 1 → (⋂ i ∈ J, (i.1 : Set (Fin d → ℝ))).Nonempty := by
    intro J hJ
    have h_sub_F : (J.image Subtype.val) ⊆ F := fun S hS ↦ by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hS; exact x.2
    have h_card_le : (J.image Subtype.val).card ≤ d + 1 := by
      have := Finset.card_image_le (s := J) (f := Subtype.val)
      omega
    have h_res := h_sub (J.image Subtype.val) h_sub_F h_card_le
    obtain ⟨x, hx⟩ := h_res
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter] at hx ⊢
    intro i hi
    exact hx i.1 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have h_main := RadonHelly.hellys_theorem (fun (i : F) ↦ i.1) h_conv' h_inter'
  obtain ⟨x, hx⟩ := h_main
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro S hS
  exact hx ⟨S, hS⟩

/-- If a family has cardinality 1, its intersection is non-empty under the transversal condition. -/
lemma family_nonempty_of_card_one (d : ℕ) (sys : ColorfulConvexSystem d)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty)
    (h_nonempty : ∀ c, (sys.families c).Nonempty)
    (c0 : Fin (d + 1)) (hc0 : (sys.families c0).card = 1) :
    (⋂ S ∈ sys.families c0, S).Nonempty := by
  obtain ⟨S0, hS0⟩ := Finset.card_eq_one.mp hc0
  have h_choice : ∀ c, ∃ S, S ∈ sys.families c := fun c ↦ h_nonempty c
  choose ch hch using h_choice
  let ch' : (c : Fin (d + 1)) → Set (Fin d → ℝ) := fun c ↦ if c = c0 then S0 else ch c
  have hch' : ∀ c, ch' c ∈ sys.families c := by
    intro c
    dsimp [ch']
    split_ifs with hc
    · subst hc; rw [hS0]; exact Finset.mem_singleton_self S0
    · exact hch c
  obtain ⟨x, hx⟩ := h_transversal ch' hch'
  simp only [Set.mem_iInter] at hx
  have hx_c0 : x ∈ S0 := by
    have hz := hx c0
    dsimp [ch'] at hz
    split_ifs at hz with hc
    · exact hz
    · exfalso; exact hc rfl
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter]
  intro S hS
  rw [hS0] at hS
  rw [Finset.mem_singleton.mp hS]
  exact hx_c0

-- ============================================================================
-- Section 2: Family Replacement Operations
-- ============================================================================

/-- Replace family k in sys with a subcollection G ⊆ sys.families k. -/
def replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k) : ColorfulConvexSystem d where
  families := fun c ↦ if c = k then G else sys.families c
  h_convex := by
    intro c S hS
    split_ifs at hS with hc
    · subst c; exact sys.h_convex k S (hG S hS)
    · exact sys.h_convex c S hS

lemma card_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k) :
    ∑ c, ((replaceFamily d sys k G hG).families c).card =
      (∑ c ∈ Finset.univ.erase k, (sys.families c).card) + G.card := by
  have h_split : ∑ c, ((replaceFamily d sys k G hG).families c).card =
      (∑ c ∈ Finset.univ.erase k, ((replaceFamily d sys k G hG).families c).card) +
      ((replaceFamily d sys k G hG).families k).card := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_comm]
  rw [h_split]
  congr 1
  · apply Finset.sum_congr rfl
    intro c hc
    have h_ne : c ≠ k := Finset.mem_erase.mp hc |>.1
    dsimp [replaceFamily]
    simp [h_ne]
  · dsimp [replaceFamily]
    simp

lemma transversal_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) → (⋂ c, choice c).Nonempty) :
    ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ (replaceFamily d sys k G hG).families c) →
      (⋂ c, choice c).Nonempty := by
  intro choice h_choice
  apply h_transversal choice
  intro c
  have hc := h_choice c
  dsimp [replaceFamily] at hc
  split_ifs at hc with hck
  · subst c; exact hG (choice k) hc
  · exact hc

lemma winner_of_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k)
    (w : Fin (d + 1))
    (hw : (⋂ S ∈ (replaceFamily d sys k G hG).families w, S).Nonempty)
    (hw_ne : w ≠ k) :
    (⋂ S ∈ sys.families w, S).Nonempty := by
  have h_fam : (replaceFamily d sys k G hG).families w = sys.families w := by
    dsimp [replaceFamily]
    simp [hw_ne]
  rwa [h_fam] at hw

-- ============================================================================
-- Section 3: Inductive Framework & Reduction
-- ============================================================================

/-- Induction statement for Colorful Helly. -/
lemma colorful_helly_inductive (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (sys : ColorfulConvexSystem d)
    (_h_size : ∑ c, (sys.families c).card = n)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty := by
  classical
  by_cases h_empty : ∃ c, sys.families c = ∅
  · exact colorful_helly_of_empty d sys h_empty
  have h_nonempty : ∀ c, (sys.families c).Nonempty := by
    intro c
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc ↦ h_empty ⟨c, hc⟩

  let Choice := (c : Fin (d + 1)) → sys.families c
  have hChoice : Nonempty Choice := by
    choose S hS using h_nonempty
    exact ⟨fun c ↦ ⟨S c, hS c⟩⟩
  have hChoice_univ : (Finset.univ : Finset Choice).Nonempty :=
    ⟨Classical.choice hChoice, Finset.mem_univ _⟩

  let witness : Choice → (Fin d → ℝ) := fun choice ↦
    Classical.choose (h_transversal (fun c ↦ (choice c : Set (Fin d → ℝ)))
      (fun c ↦ (choice c).property))
  have witness_mem (choice : Choice) (c : Fin (d + 1)) :
      witness choice ∈ (choice c : Set (Fin d → ℝ)) := by
    exact Set.mem_iInter.mp (Classical.choose_spec
      (h_transversal (fun c ↦ (choice c : Set (Fin d → ℝ)))
        (fun c ↦ (choice c).property))) c

  let W : Set (Fin d → ℝ) := Set.range witness
  let K (S : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := convexHull ℝ (W ∩ S)
  have hW_finite : W.Finite := Set.finite_range witness
  have hK_compact (S : Set (Fin d → ℝ)) : IsCompact (K S) := by
    exact (hW_finite.inter_of_left S).isCompact_convexHull ℝ
  have hK_convex (S : Set (Fin d → ℝ)) : Convex ℝ (K S) :=
    convex_convexHull ℝ (W ∩ S)
  have hK_subset (c : Fin (d + 1)) (S : sys.families c) :
      K (S : Set (Fin d → ℝ)) ⊆ (S : Set (Fin d → ℝ)) := by
    exact convexHull_min Set.inter_subset_right (sys.h_convex c S S.property)
  have witness_mem_K (choice : Choice) (c : Fin (d + 1)) :
      witness choice ∈ K (choice c : Set (Fin d → ℝ)) := by
    apply subset_convexHull ℝ
    exact ⟨⟨choice, rfl⟩, witness_mem choice c⟩

  let Q (choice : Choice) : Set (Fin d → ℝ) :=
    ⋂ c, K (choice c : Set (Fin d → ℝ))
  have hQ_nonempty (choice : Choice) : (Q choice).Nonempty := by
    exact ⟨witness choice, Set.mem_iInter_of_mem (witness_mem_K choice)⟩
  have hQ_compact (choice : Choice) : IsCompact (Q choice) := by
    let c0 : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
    apply (hK_compact (choice c0 : Set (Fin d → ℝ))).of_isClosed_subset
    · exact isClosed_iInter (fun c ↦ (hK_compact
        (choice c : Set (Fin d → ℝ))).isClosed)
    · exact Set.iInter_subset (fun c ↦ K (choice c : Set (Fin d → ℝ))) c0

  have h_min (choice : Choice) :
      ∃ x ∈ Q choice, IsMinOn (euclideanSq d) (Q choice) x :=
    (hQ_compact choice).exists_isMinOn (hQ_nonempty choice)
      (continuous_euclideanSq d).continuousOn
  let closest : Choice → (Fin d → ℝ) := fun choice ↦ Classical.choose (h_min choice)
  have closest_mem (choice : Choice) : closest choice ∈ Q choice :=
    (Classical.choose_spec (h_min choice)).1
  have closest_min (choice : Choice) {x : Fin d → ℝ} (hx : x ∈ Q choice) :
      euclideanSq d (closest choice) ≤ euclideanSq d x :=
    (Classical.choose_spec (h_min choice)).2 hx

  obtain ⟨best, -, hbest⟩ := Finset.exists_max_image (Finset.univ : Finset Choice)
    (fun choice ↦ euclideanSq d (closest choice)) hChoice_univ

  let extSet : Option (Fin (d + 1)) → Set (Fin d → ℝ)
    | none => {x | euclideanSq d x < euclideanSq d (closest best)}
    | some c => K (best c : Set (Fin d → ℝ))
  have h_ext_convex (i : Option (Fin (d + 1))) : Convex ℝ (extSet i) := by
    cases i with
    | none => exact convex_euclideanSq_lt d (euclideanSq d (closest best))
    | some c => exact hK_convex (best c : Set (Fin d → ℝ))
  have h_ext_empty : ¬(⋂ i, extSet i).Nonempty := by
    rintro ⟨x, hx⟩
    have hxQ : x ∈ Q best := by
      rw [Set.mem_iInter]
      intro c
      exact Set.mem_iInter.mp hx (some c)
    have hxlt : euclideanSq d x < euclideanSq d (closest best) :=
      Set.mem_iInter.mp hx none
    exact (not_lt_of_ge (closest_min best hxQ)) hxlt
  have h_small : ∃ J : Finset (Option (Fin (d + 1))), J.card ≤ d + 1 ∧
      ¬(⋂ i ∈ J, extSet i).Nonempty := by
    by_contra h
    have h_sub : ∀ J : Finset (Option (Fin (d + 1))), J.card ≤ d + 1 →
        (⋂ i ∈ J, extSet i).Nonempty := by
      intro J hJ
      by_contra hne
      exact h ⟨J, hJ, hne⟩
    exact h_ext_empty (RadonHelly.hellys_theorem extSet h_ext_convex h_sub)
  obtain ⟨J, hJ_card, hJ_empty⟩ := h_small
  have hnone : none ∈ J := by
    by_contra hnone
    apply hJ_empty
    refine ⟨closest best, ?_⟩
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    cases i with
    | none => exact (hnone hi).elim
    | some c => exact Set.mem_iInter.mp (closest_mem best) c

  let colored : Finset (Option (Fin (d + 1))) :=
    Finset.image some (Finset.univ : Finset (Fin (d + 1)))
  have h_erase_card : (J.erase none).card < colored.card := by
    rw [Finset.card_erase_of_mem hnone, show colored.card = d + 1 by
      dsimp [colored]
      rw [Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_univ,
        Fintype.card_fin]]
    omega
  obtain ⟨i, hi_colored, hi_erase⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card h_erase_card
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi_colored
  have hkJ : some k ∉ J := by
    intro hk
    exact hi_erase (Finset.mem_erase.mpr ⟨Option.some_ne_none k, hk⟩)

  have determinant_lower {x : Fin d → ℝ}
      (hx : ∀ c, some c ∈ J → x ∈ K (best c : Set (Fin d → ℝ))) :
      euclideanSq d (closest best) ≤ euclideanSq d x := by
    by_contra hle
    apply hJ_empty
    refine ⟨x, ?_⟩
    rw [Set.mem_iInter]
    intro i
    rw [Set.mem_iInter]
    intro hi
    cases i with
    | none => exact lt_of_not_ge hle
    | some c => exact hx c hi

  refine ⟨k, ⟨closest best, ?_⟩⟩
  rw [Set.mem_iInter]
  intro S
  rw [Set.mem_iInter]
  intro hS
  let Sk : sys.families k := ⟨S, hS⟩
  let replacement : Choice := fun c ↦ if hc : c = k then hc ▸ Sk else best c
  have replacement_eq (c : Fin (d + 1)) (hc : c ≠ k) : replacement c = best c := by
    simp [replacement, hc]
  have hrep_ge : euclideanSq d (closest best) ≤ euclideanSq d (closest replacement) := by
    apply determinant_lower
    intro c hcJ
    have hck : c ≠ k := by
      intro h
      subst c
      exact hkJ hcJ
    rw [← replacement_eq c hck]
    exact Set.mem_iInter.mp (closest_mem replacement) c
  have hrep_le : euclideanSq d (closest replacement) ≤ euclideanSq d (closest best) :=
    hbest replacement (Finset.mem_univ replacement)
  have hrep_value : euclideanSq d (closest replacement) = euclideanSq d (closest best) :=
    le_antisymm hrep_le hrep_ge
  have hrep_point : closest replacement = closest best := by
    by_contra hne
    let midpoint := (2 : ℝ)⁻¹ • closest replacement + (2 : ℝ)⁻¹ • closest best
    have hmid_constraints : ∀ c, some c ∈ J →
        midpoint ∈ K (best c : Set (Fin d → ℝ)) := by
      intro c hcJ
      have hck : c ≠ k := by
        intro h
        subst c
        exact hkJ hcJ
      apply hK_convex (best c : Set (Fin d → ℝ))
      · rw [← replacement_eq c hck]
        exact Set.mem_iInter.mp (closest_mem replacement) c
      · exact Set.mem_iInter.mp (closest_mem best) c
      · norm_num
      · norm_num
      · norm_num
    have hmid_ge := determinant_lower hmid_constraints
    have hmid_lt : euclideanSq d midpoint < euclideanSq d (closest replacement) := by
      exact euclideanSq_midpoint_lt hne hrep_value
    linarith
  have hrep_K : closest replacement ∈ K S := by
    have := Set.mem_iInter.mp (closest_mem replacement) k
    simpa [replacement, Sk] using this
  rw [hrep_point] at hrep_K
  exact hK_subset k Sk hrep_K

-- ============================================================================
-- Section 4: Main Theorem (Bárány 1982)
-- ============================================================================

/-- Main Theorem: Bárány's Colorful Helly Theorem (1982).
    If all colorful selections of d+1 sets intersect,
    then at least one family has a non-empty global intersection. -/
theorem colorful_helly (d : ℕ) (hd : 1 ≤ d) (sys : ColorfulConvexSystem d)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty :=
  colorful_helly_inductive d hd (∑ c, (sys.families c).card) sys rfl h_transversal

end ColorfulHelly

#print axioms ColorfulHelly.colorful_helly_inductive
#print axioms ColorfulHelly.colorful_helly
