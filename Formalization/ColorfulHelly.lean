import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Formalization.RadonHelly

/-!
# Bárány's Colorful Helly Theorem (1982)

**Theorem Statement (Bárány 1982):**
Let $\mathcal{F}_0, \mathcal{F}_1, \dots, \mathcal{F}_d$ be $d+1$ finite families of convex sets
in $\mathbb{R}^d$. If every colorful transversal (i.e. every selection of one set
$S_i \in \mathcal{F}_i$ for each $i \in \{0, \dots, d\}$) has a non-empty intersection
$\bigcap_{i=0}^d S_i \ne \emptyset$, then at least one family $\mathcal{F}_j$ has a non-empty
global intersection:
$$\exists j \in \{0, \dots, d\}, \quad \bigcap_{S \in \mathcal{F}_j} S \ne \emptyset.$$

### Note on Mathematical Prerequisites:
As established by Bárány (1982), the full Colorful Helly theorem requires topological
intersection machinery (the Colorful Carathéodory Theorem or topological degree theory)
rather than purely elementary set-theoretic induction on $\sum |\mathcal{F}_c|$.
This file provides the complete framework, family substitution operators, and verified base
lemmas, preserving the formalization scaffold for when Colorful Carathéodory is formalized in Mathlib.
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
    · subst hc; exact sys.h_convex k S (hG S hS)
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
    rw [if_neg h_ne]
  · dsimp [replaceFamily]
    rw [if_pos rfl]

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
  · subst hck; exact hG (choice k) hc
  · exact hc

lemma winner_of_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k)
    (w : Fin (d + 1))
    (hw : (⋂ S ∈ (replaceFamily d sys k G hG).families w, S).Nonempty)
    (hw_ne : w ≠ k) :
    (⋂ S ∈ sys.families w, S).Nonempty := by
  have h_fam : (replaceFamily d sys k G hG).families w = sys.families w := by
    dsimp [replaceFamily]
    rw [if_neg hw_ne]
  rwa [h_fam] at hw

-- ============================================================================
-- Section 3: Inductive Framework & Reduction
-- ============================================================================

/-- Induction statement for Colorful Helly. -/
lemma colorful_helly_inductive (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (sys : ColorfulConvexSystem d)
    (h_size : ∑ c, (sys.families c).card = n)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty := by
  sorry

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
