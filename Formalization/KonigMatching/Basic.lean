import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Choose

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false

/-!
# Definitions and Weak Duality for Matchings, Vertex Covers, and Independent Sets

This module formalizes the core invariants of matching theory and vertex covers in finite simple graphs:
- Matching, vertex cover, and independent set predicates
- Matching number $\nu(G)$, vertex cover number $\tau(G)$, and independence number $\alpha(G)$
- The fundamental Weak Duality theorem: $\nu(G) \le \tau(G)$
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

lemma fin2_cases (y : Fin 2) : y = 0 ∨ y = 1 := by revert y; decide

/-- Two edges in $G$ share a common endpoint vertex. -/
def EdgesShareEndpoint (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v : V, v ∈ e₁ ∧ v ∈ e₂

/-- A set of edges $M \subseteq \operatorname{Sym2}(V)$ is a matching in $G$ if all edges belong to $G$
and no two distinct edges share a vertex. -/
def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ¬ EdgesShareEndpoint e₁ e₂)

/-- A set of vertices $C \subseteq V$ is a vertex cover of $G$ if every edge has at least
one endpoint in $C$. -/
def IsVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ u v : V, G.Adj u v → u ∈ C ∨ v ∈ C

/-- The empty edge set is always a valid matching. -/
theorem isMatching_empty (G : SimpleGraph V) : IsMatching G ∅ :=
  ⟨by simp, by simp⟩

/-- The full vertex set is always a valid vertex cover. -/
theorem isVertexCover_univ (G : SimpleGraph V) : IsVertexCover G Finset.univ :=
  fun _ _ _ => Or.inl (Finset.mem_univ _)

/-- The matching number $\nu(G)$: maximum size of a matching in $G$. -/
noncomputable def matchingNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ M : Finset (Sym2 V), IsMatching G M ∧ M.card = k }

/-- The vertex cover number $\tau(G)$: minimum size of a vertex cover in $G$. -/
noncomputable def vertexCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }

/-- An independent set in $G$ is a set of pairwise non-adjacent vertices. -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

/-- The empty vertex set is always an independent set. -/
theorem isIndependentSet_empty (G : SimpleGraph V) : IsIndependentSet G ∅ := by
  simp [IsIndependentSet]

/-- The independence number $\alpha(G)$: maximum size of an independent set in $G$. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset V, IsIndependentSet G S ∧ S.card = k }

/-- An independent set corresponds bijectively to the complement of a vertex cover. -/
theorem isIndependentSet_iff_isVertexCover_compl (G : SimpleGraph V) (S : Finset V) :
    IsIndependentSet G S ↔ IsVertexCover G (Finset.univ \ S) := by
  simp [IsIndependentSet, IsVertexCover, or_iff_not_and_not]
  exact ⟨fun h u v hadj hu hv => h u hu v hv hadj, fun h u hu v hv hadj => h u v hadj hu hv⟩

/--
**Weak Duality for Matchings and Vertex Covers**:
Any matching $M$ and any vertex cover $C$ satisfy $|M| \le |C|$, since each vertex in $C$
can cover at most one edge of the vertex-disjoint family $M$.
-/
theorem matching_card_le_vertexCover_card (G : SimpleGraph V) {M : Finset (Sym2 V)} {C : Finset V}
    (hM : IsMatching G M) (hC : IsVertexCover G C) :
    M.card ≤ C.card := by
  have : ∀ e ∈ M, ∃ v ∈ C, v ∈ e := fun e he => Sym2.inductionOn e (fun u v hadj =>
    (hC u v hadj).elim (⟨u, ·, Sym2.mem_mk_left u v⟩) (⟨v, ·, Sym2.mem_mk_right u v⟩)) (hM.1 e he)
  choose f hfC hfe using this
  have h_inj : ∀ (e₁ e₂ : M), f e₁.1 e₁.2 = f e₂.1 e₂.2 → e₁ = e₂ :=
    fun ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ heq => Subtype.ext <| by_contra fun hne =>
      hM.2 e₁ h₁ e₂ h₂ hne ⟨f e₁ h₁, hfe e₁ h₁, heq ▸ hfe e₂ h₂⟩
  rw [← Finset.card_attach (s := M), ← Finset.card_image_of_injective _ h_inj]
  exact Finset.card_le_card (Finset.image_subset_iff.mpr fun ⟨e, he⟩ _ => hfC e he)

/--
**Weak Duality Theorem**:
For any finite simple graph $G$, the matching number is bounded by the vertex cover number:
$$\nu(G) \le \tau(G)$$
-/
theorem weak_duality (G : SimpleGraph V) :
    matchingNumber G ≤ vertexCoverNumber G := by
  refine le_csInf ⟨_, _, isVertexCover_univ G, rfl⟩ ?_
  rintro _ ⟨C, hC, rfl⟩
  refine csSup_le ⟨_, _, isMatching_empty G, rfl⟩ ?_
  rintro _ ⟨M, hM, rfl⟩
  exact matching_card_le_vertexCover_card G hM hC

end SimpleGraph
