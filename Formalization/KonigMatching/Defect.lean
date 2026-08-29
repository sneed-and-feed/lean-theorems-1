import Formalization.KonigMatching.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

/-!
# Hall Defect and Matching Extraction in Bipartite Graphs

This module develops the deficiency theory and Hall reduction machinery:
- Maximal deficiency subset existence (`exists_max_defect`)
- Vertex cover construction from maximal deficiency subsets (`isVertexCover_bipartite_defect`, `bipartite_defect_cover_card`)
- Augmented neighborhood construction for Hall's condition (`augmentedNeighbors`, `hall_condition_augmented`)
- Extraction of matching from Hall's injection (`exists_matching_from_hall_inj`)
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/--
Existence of a maximal deficiency subset $S_0 \subseteq A$ for the defect form of Hall's condition.
-/
theorem exists_max_defect (G : SimpleGraph V) (A : Finset V) :
    ∃ (S₀ : Finset V) (d : ℕ), S₀ ⊆ A ∧
      (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card ∧
      d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card ∧
      ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  let f (S : Finset V) : ℕ := S.card - (S.biUnion (fun a => G.neighborFinset a)).card
  obtain ⟨S₁, hS₁, hmax⟩ := Finset.exists_max_image A.powerset f ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset A)⟩
  by_cases hd : f S₁ = 0
  · refine ⟨∅, 0, Finset.empty_subset A, by simp, by simp, fun S hS => ?_⟩
    have := hmax S (Finset.mem_powerset.mpr hS); dsimp [f] at hd this; omega
  · refine ⟨S₁, f S₁, Finset.mem_powerset.mp hS₁, by dsimp [f] at *; omega, rfl, fun S hS => ?_⟩
    have := hmax S (Finset.mem_powerset.mpr hS); dsimp [f] at *; omega

/-- In a 2-colored graph, neighbors of vertices colored 0 all have color 1. -/
lemma bipartite_neighborFinset_subset (G : SimpleGraph V) (c : G.Coloring (Fin 2)) (S : Finset V)
    (hS : ∀ x ∈ S, c x = 0) :
    S.biUnion (fun a => G.neighborFinset a) ⊆ Finset.filter (fun v => c v = 1) Finset.univ := by
  rintro b hb
  obtain ⟨a, ha, hadj⟩ := Finset.mem_biUnion.mp hb
  have := c.valid ((G.mem_neighborFinset a b).mp hadj)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases fin2_cases (c b) with
  | inl h0 => cases this (by rw [hS a ha, h0])
  | inr h1 => exact h1

/-- Construction of a vertex cover $(A \setminus S_0) \cup N(S_0)$ from a defect set $S_0 \subseteq A$. -/
lemma isVertexCover_bipartite_defect (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A S₀ : Finset V) (hA : A = Finset.filter (fun v => c v = 0) Finset.univ) (_hS₀ : S₀ ⊆ A) :
    IsVertexCover G ((A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)) := by
  have h_cov (x y : V) (hxy : G.Adj x y) (hx0 : c x = 0) :
      x ∈ (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a) ∨ y ∈ (A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a) := by
    by_cases hxS : x ∈ S₀
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hxS, (G.mem_neighborFinset x y).mpr hxy⟩))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨by simp [hA, hx0], hxS⟩))
  intro u v hadj
  rcases fin2_cases (c u) with hu0 | hu1
  · exact h_cov u v hadj hu0
  · rcases fin2_cases (c v) with hv0 | hv1
    · exact (h_cov v u hadj.symm hv0).symm
    · exact (c.valid hadj (by rw [hu1, hv1])).elim

/-- Cardinality of the vertex cover $(A \setminus S_0) \cup N(S_0)$ is exactly $|A| - d$. -/
lemma bipartite_defect_cover_card (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A S₀ : Finset V) (d : ℕ)
    (hA : A = Finset.filter (fun v => c v = 0) Finset.univ)
    (hS₀ : S₀ ⊆ A)
    (hd_eq : d = S₀.card - (S₀.biUnion (fun a => G.neighborFinset a)).card)
    (hS₀_le : (S₀.biUnion (fun a => G.neighborFinset a)).card ≤ S₀.card) :
    ((A \ S₀) ∪ S₀.biUnion (fun a => G.neighborFinset a)).card = A.card - d := by
  have h_disj : Disjoint (A \ S₀) (S₀.biUnion (fun a => G.neighborFinset a)) := by
    refine Disjoint.mono Finset.sdiff_subset (bipartite_neighborFinset_subset G c S₀ ?_) ?_
    · intro x hx
      have := hS₀ hx
      rw [hA, Finset.mem_filter] at this
      exact this.2
    · rw [hA, Finset.disjoint_left]
      intro x hxA hxB
      have := (Finset.mem_filter.mp hxA).2.symm.trans (Finset.mem_filter.mp hxB).2
      revert this; decide
  rw [Finset.card_union_of_disjoint h_disj, Finset.card_sdiff, Finset.inter_eq_left.mpr hS₀, hd_eq]
  have := Finset.card_le_card hS₀; omega

/-- Augmented neighborhood family for Hall's condition with defect $d$. -/
noncomputable def augmentedNeighbors (G : SimpleGraph V) (d : ℕ) (a : V) : Finset (V ⊕ Fin d) :=
  (G.neighborFinset a).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr

lemma augmentedNeighbors_biUnion (G : SimpleGraph V) (d : ℕ) {S : Finset V} (hS : S.Nonempty) :
    S.biUnion (augmentedNeighbors G d) =
      (S.biUnion (fun a => G.neighborFinset a)).image Sum.inl ∪ (Finset.univ : Finset (Fin d)).image Sum.inr := by
  ext (v | i) <;> simp [augmentedNeighbors, hS.exists_mem]

lemma card_augmentedNeighbors_biUnion (G : SimpleGraph V) (d : ℕ) {S : Finset V} (hS : S.Nonempty) :
    (S.biUnion (augmentedNeighbors G d)).card = (S.biUnion (fun a => G.neighborFinset a)).card + d := by
  rw [augmentedNeighbors_biUnion G d hS, Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]),
      Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_image_of_injective _ Sum.inr_injective,
      Finset.card_fin]

/-- Hall's condition holds for the augmented neighborhood family on the subtype $A$. -/
lemma hall_condition_augmented (G : SimpleGraph V) (A : Finset V) (d : ℕ)
    (hd_max : ∀ S ⊆ A, S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card + d)
    (S' : Finset A) :
    S'.card ≤ (S'.biUnion (fun a => augmentedNeighbors G d a.val)).card := by
  by_cases hS' : S'.Nonempty
  · have h_sub : S'.image Subtype.val ⊆ A := Finset.image_subset_iff.mpr fun x _ => x.2
    have h_biUnion : (S'.image Subtype.val).biUnion (augmentedNeighbors G d) =
        S'.biUnion (fun a => augmentedNeighbors G d a.val) := by ext x; simp [augmentedNeighbors]
    rw [← Finset.card_image_of_injective S' Subtype.val_injective, ← h_biUnion,
        card_augmentedNeighbors_biUnion G d (hS'.image _)]
    exact hd_max _ h_sub
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS']; simp

/-- Extraction of a valid matching $M$ of cardinality at least $|A| - d$ from Hall's injection. -/
lemma exists_matching_from_hall_inj (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (A : Finset V) (d : ℕ)
    (hA : A = Finset.filter (fun v => c v = 0) Finset.univ)
    (f : A → V ⊕ Fin d) (hf_inj : Function.Injective f)
    (hf_mem : ∀ a : A, f a ∈ augmentedNeighbors G d a.val) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧ A.card - d ≤ M.card := by
  let A_mat : Finset A := Finset.filter (fun a => ∃ v : V, f a = Sum.inl v) Finset.univ
  have h_compl_card : (Finset.univ \ A_mat : Finset A).card ≤ d := by
    have h_inr : ∀ a ∈ (Finset.univ \ A_mat : Finset A), ∃ i : Fin d, f a = Sum.inr i := by
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter, not_exists, A_mat] at ha
      cases hfa : f a with
      | inl v => exact (ha v hfa).elim
      | inr i => exact ⟨i, rfl⟩
    choose finr hfinr using h_inr
    have h_inj' : ∀ (x y : { a : A // a ∈ Finset.univ \ A_mat }), finr x.1 x.2 = finr y.1 y.2 → x = y :=
      fun ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ heq => Subtype.ext (hf_inj (by rw [hfinr a₁ h₁, hfinr a₂ h₂, heq]))
    have := Finset.card_le_card (Finset.subset_univ ((Finset.univ \ A_mat).attach.image (fun ⟨a, ha⟩ => finr a ha)))
    rw [Finset.card_image_of_injective _ (fun _ _ => h_inj' _ _), Finset.card_attach, Finset.card_fin] at this
    exact this
  have hA_mat_card : A.card - d ≤ A_mat.card := by
    have h_split := Finset.card_sdiff (s := A_mat) (t := Finset.univ)
    rw [Finset.inter_univ, Finset.card_univ, Fintype.card_coe] at h_split
    omega
  have hg_choice : ∀ a ∈ A_mat, ∃ v : V, f a = Sum.inl v ∧ G.Adj a.val v := by
    intro a ha
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp ha).2
    have hfa := hf_mem a
    simp only [augmentedNeighbors, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hfa
    rcases hfa with (⟨v', hv', heq⟩ | ⟨i, heq⟩)
    · exact ⟨v, hv, (G.mem_neighborFinset a.val v).mp (by cases Sum.inl.inj (hv.symm.trans heq.symm); exact hv')⟩
    · cases hv.symm.trans heq.symm
  choose g hg_f hg_adj using hg_choice
  let M : Finset (Sym2 V) := A_mat.attach.image (fun ⟨a, ha⟩ => s(a.val, g a ha))
  have ha_c : ∀ a : A, c a.val = 0 := fun a => by
    have ha := a.property
    have : a.val ∈ Finset.filter (fun v => c v = 0) Finset.univ := hA ▸ ha
    exact (Finset.mem_filter.mp this).2
  have hg_c : ∀ (a : A) (ha : a ∈ A_mat), c (g a ha) = 1 := fun a ha =>
    (fin2_cases (c (g a ha))).resolve_left fun h0 => c.valid (hg_adj a ha) (by rw [ha_c a, h0])
  have hM_card : M.card = A_mat.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · rintro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ heq
      rcases Sym2.eq_iff.mp heq with (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Subtype.ext (Subtype.ext h1)
      · exfalso; have := congrArg c h1; rw [ha_c a₁, hg_c a₂ ha₂] at this; revert this; decide
  refine ⟨M, ⟨?_, ?_⟩, by omega⟩
  · rintro e he
    obtain ⟨⟨a, ha⟩, -, rfl⟩ := Finset.mem_image.mp he
    exact hg_adj a ha
  · rintro e₁ he₁ e₂ he₂ hne ⟨w, hw₁, hw₂⟩
    obtain ⟨⟨a₁, ha₁⟩, -, rfl⟩ := Finset.mem_image.mp he₁
    obtain ⟨⟨a₂, ha₂⟩, -, rfl⟩ := Finset.mem_image.mp he₂
    rcases Sym2.mem_iff.mp hw₁ with (hw1 | hw1) <;> rcases Sym2.mem_iff.mp hw₂ with (hw2 | hw2)
    · have h_eq : a₁.val = a₂.val := hw1.symm.trans hw2
      have : a₁ = a₂ := Subtype.ext h_eq
      subst this; exact hne rfl
    · exfalso; have := congrArg c (hw1.symm.trans hw2 : a₁.val = g a₂ ha₂); rw [ha_c a₁, hg_c a₂ ha₂] at this; revert this; decide
    · exfalso; have := congrArg c (hw1.symm.trans hw2 : g a₁ ha₁ = a₂.val); rw [hg_c a₁ ha₁, ha_c a₂] at this; revert this; decide
    · have hg_eq : g a₁ ha₁ = g a₂ ha₂ := hw1.symm.trans hw2
      have hf_eq : f a₁ = f a₂ := by rw [hg_f a₁ ha₁, hg_f a₂ ha₂, hg_eq]
      have : a₁ = a₂ := hf_inj hf_eq
      subst this; exact hne rfl

end SimpleGraph
