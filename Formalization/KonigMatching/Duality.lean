import Formalization.KonigMatching.Basic
import Formalization.KonigMatching.Defect
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Classical

/-!
# Strong Duality and Gallai Identities for Bipartite Graphs

This module formalizes the main duality theorems and structural invariants:
- Strong min-max duality for bipartite graphs: $\nu(G) = \tau(G)$ (`konig_duality`)
- Gallai's identity relating vertex covers and independent sets: $\alpha(G) + \tau(G) = |V|$ (`gallai_independence_vertex_cover`)
- Kőnig's formula for independent sets in bipartite graphs: $\alpha(G) + \nu(G) = |V|$ (`konig_independence_matching`)
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

/--
**Strong Duality Inequality in Bipartite Graphs**:
For any $2$-colorable graph $G$, the vertex cover number is bounded by the matching number:
$$\tau(G) \le \nu(G)$$
-/
theorem konig_duality_le (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    vertexCoverNumber G ≤ matchingNumber G := by
  obtain ⟨c⟩ := h_bip
  let A := Finset.filter (fun v => c v = 0) Finset.univ
  obtain ⟨S₀, d, hS₀_sub, hS₀_le, hd_eq, hd_max⟩ := exists_max_defect G A
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective _).mp
    (hall_condition_augmented G A d hd_max)
  obtain ⟨M, hM_match, hM_card⟩ := exists_matching_from_hall_inj G c A d rfl f hf_inj hf_mem
  have hC_cov := isVertexCover_bipartite_defect G c A S₀ rfl hS₀_sub
  have hC_card := bipartite_defect_cover_card G c A S₀ d rfl hS₀_sub hd_eq hS₀_le
  have h_tau_le : vertexCoverNumber G ≤ A.card - d :=
    hC_card ▸ csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨_, hC_cov, rfl⟩
  have h_le_nu : M.card ≤ matchingNumber G :=
    le_csSup ⟨Fintype.card (Sym2 V), by rintro _ ⟨M', -, rfl⟩; exact Finset.card_le_univ M'⟩ ⟨M, hM_match, rfl⟩
  omega

/--
**Kőnig–Egerváry Theorem (1931)**:
In any bipartite ($2$-colorable) graph $G$, the maximum size of a matching equals the minimum
size of a vertex cover (strong min-max duality):
$$\nu(G) = \tau(G)$$
-/
theorem konig_duality (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    matchingNumber G = vertexCoverNumber G :=
  le_antisymm (weak_duality G) (konig_duality_le G h_bip)

/--
**Gallai's Identity for Vertex Covers and Independent Sets (1959)**:
For any finite graph $G$, the independence number and vertex cover number sum to $|V|$:
$$\alpha(G) + \tau(G) = |V|$$
-/
theorem gallai_independence_vertex_cover (G : SimpleGraph V) :
    independenceNumber G + vertexCoverNumber G = Fintype.card V := by
  have hSC_nonempty : { k : ℕ | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k }.Nonempty :=
    ⟨Fintype.card V, Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  obtain ⟨C, hC_cov, hC_card⟩ := Nat.sInf_mem hSC_nonempty
  have hS_ind : IsIndependentSet G (Finset.univ \ C) := by
    rw [isIndependentSet_iff_isVertexCover_compl, Finset.sdiff_sdiff_eq_self (Finset.subset_univ C)]; exact hC_cov
  have hS_card : (Finset.univ \ C).card = Fintype.card V - vertexCoverNumber G := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hC_card]
    rfl
  have h_le1 : Fintype.card V - vertexCoverNumber G ≤ independenceNumber G :=
    le_csSup ⟨Fintype.card V, by rintro _ ⟨S, -, rfl⟩; exact Finset.card_le_univ S⟩ ⟨_, hS_ind, hS_card⟩
  have h_ind_le : independenceNumber G ≤ Fintype.card V - vertexCoverNumber G := by
    refine csSup_le ⟨0, ∅, isIndependentSet_empty G, rfl⟩ ?_
    rintro _ ⟨S, hS, rfl⟩
    have h_tau : vertexCoverNumber G ≤ (Finset.univ \ S).card :=
      csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨_, (isIndependentSet_iff_isVertexCover_compl G S).mp hS, rfl⟩
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at h_tau
    have := Finset.card_le_univ S; omega
  have h_tau_le : vertexCoverNumber G ≤ Fintype.card V :=
    csInf_le ⟨0, fun _ _ => Nat.zero_le _⟩ ⟨Finset.univ, isVertexCover_univ G, Finset.card_univ⟩
  omega

/--
**Kőnig's Min-Max Formula for Independent Sets in Bipartite Graphs**:
In a bipartite graph, the independence number satisfies $\alpha(G) = |V| - \nu(G)$.
-/
theorem konig_independence_matching (G : SimpleGraph V) (h_bip : G.Colorable 2) :
    independenceNumber G + matchingNumber G = Fintype.card V :=
  konig_duality G h_bip ▸ gallai_independence_vertex_cover G

end SimpleGraph
