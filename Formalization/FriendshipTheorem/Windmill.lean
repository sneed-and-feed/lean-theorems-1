import Formalization.FriendshipTheorem.Basic
import Formalization.FriendshipTheorem.Politician
import Formalization.FriendshipTheorem.Walks
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The 2-Regular Case and Windmill Graph Properties

This module handles the 2-regular base case for friendship graphs and establishes
the windmill graph structure ($Wd(k, 2)$):
1. **2-Regular Friendship Graphs**: Any 2-regular friendship graph on $\ge 3$ vertices
   is isomorphic to the triangle $K_3$, in which every vertex is universal.
2. **Windmill Structure**: A graph satisfying the friendship property consists of $k$
   triangles sharing a single universal vertex (politician).

## Main Theorems
* `two_regular_has_universal`: In a 2-regular friendship graph with $\ge 3$ vertices,
  there exists a universal vertex (the entire graph is a single triangle $K_3$).
-/

namespace FriendshipTheorem

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a 2-regular friendship graph with at least 3 vertices, every vertex belongs to a
triangle $K_3$, the entire graph is $K_3$, and any vertex is universal. -/
theorem two_regular_has_universal (h_friend : HasFriendshipProperty G)
    (h_reg : ∀ v : V, G.degree v = 2) (h_card : 3 ≤ Fintype.card V) :
    ∃ w : V, IsUniversalVertex G w := by
  have h_nonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u⟩ := h_nonempty
  have h_deg_u : (G.neighborFinset u).card = 2 := h_reg u
  obtain ⟨v1, v2, hv12, hNu⟩ := Finset.card_eq_two.mp h_deg_u
  have hv1_in : v1 ∈ G.neighborFinset u := by
    rw [hNu]
    exact Finset.mem_insert_self v1 {v2}
  have hv2_in : v2 ∈ G.neighborFinset u := by
    rw [hNu, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr rfl
  have hadj_uv1 : G.Adj u v1 := by rwa [G.mem_neighborFinset] at hv1_in
  have hadj_uv2 : G.Adj u v2 := by rwa [G.mem_neighborFinset] at hv2_in
  have hu_ne_v1 : u ≠ v1 := hadj_uv1.ne
  have hc_mem := commonNeighbor_mem_inter h_friend hu_ne_v1
  rw [Finset.mem_inter] at hc_mem
  have hc_in_Nu : commonNeighbor h_friend hu_ne_v1 ∈ G.neighborFinset u := hc_mem.1
  have hc_in_Nv1 : commonNeighbor h_friend hu_ne_v1 ∈ G.neighborFinset v1 := hc_mem.2
  have hc_ne_v1 : commonNeighbor h_friend hu_ne_v1 ≠ v1 := commonNeighbor_ne_right h_friend hu_ne_v1
  have hc_eq_v2 : commonNeighbor h_friend hu_ne_v1 = v2 := by
    rw [hNu, Finset.mem_insert, Finset.mem_singleton] at hc_in_Nu
    rcases hc_in_Nu with (hc1 | hc2)
    · exact (hc_ne_v1 hc1).elim
    · exact hc2
  have hadj_v1v2 : G.Adj v1 v2 := by
    have : G.Adj v1 (commonNeighbor h_friend hu_ne_v1) := by rwa [G.mem_neighborFinset] at hc_in_Nv1
    rwa [hc_eq_v2] at this
  have h_Nv1_sub : {u, v2} ⊆ G.neighborFinset v1 := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl)
    · rw [G.mem_neighborFinset]
      exact hadj_uv1.symm
    · rw [G.mem_neighborFinset]
      exact hadj_v1v2
  have hu_ne_v2 : u ≠ v2 := hadj_uv2.ne
  have h_card_pair1 : ({u, v2} : Finset V).card = 2 := Finset.card_pair hu_ne_v2
  have h_deg_v1 : (G.neighborFinset v1).card = 2 := h_reg v1
  have h_Nv1_eq : G.neighborFinset v1 = {u, v2} := by
    have := Finset.eq_of_subset_of_card_le h_Nv1_sub (by rw [h_deg_v1, h_card_pair1])
    exact this.symm
  have h_Nv2_sub : {u, v1} ⊆ G.neighborFinset v2 := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl)
    · rw [G.mem_neighborFinset]
      exact hadj_uv2.symm
    · rw [G.mem_neighborFinset]
      exact hadj_v1v2.symm
  have h_card_pair2 : ({u, v1} : Finset V).card = 2 := Finset.card_pair hu_ne_v1
  have h_deg_v2 : (G.neighborFinset v2).card = 2 := h_reg v2
  have h_Nv2_eq : G.neighborFinset v2 = {u, v1} := by
    have := Finset.eq_of_subset_of_card_le h_Nv2_sub (by rw [h_deg_v2, h_card_pair2])
    exact this.symm
  have h_all_mem (x : V) : x = u ∨ x = v1 ∨ x = v2 := by
    by_contra h_not
    have hxu : x ≠ u := fun h => h_not (Or.inl h)
    have hxv1 : x ≠ v1 := fun h => h_not (Or.inr (Or.inl h))
    have hxv2 : x ≠ v2 := fun h => h_not (Or.inr (Or.inr h))
    have hu_ne_x : u ≠ x := hxu.symm
    have hy_mem := commonNeighbor_mem_inter h_friend hu_ne_x
    rw [Finset.mem_inter] at hy_mem
    have hy_in_Nu : commonNeighbor h_friend hu_ne_x ∈ G.neighborFinset u := hy_mem.1
    have hy_in_Nx : commonNeighbor h_friend hu_ne_x ∈ G.neighborFinset x := hy_mem.2
    have hadj_xy : G.Adj x (commonNeighbor h_friend hu_ne_x) := by rwa [G.mem_neighborFinset] at hy_in_Nx
    rw [hNu, Finset.mem_insert, Finset.mem_singleton] at hy_in_Nu
    rcases hy_in_Nu with (hy1 | hy2)
    · have hadj_xv1 : G.Adj x v1 := hy1 ▸ hadj_xy
      have : x ∈ G.neighborFinset v1 := by
        rw [G.mem_neighborFinset]
        exact hadj_xv1.symm
      rw [h_Nv1_eq, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with (rfl | rfl)
      · exact hxu rfl
      · exact hxv2 rfl
    · have hadj_xv2 : G.Adj x v2 := hy2 ▸ hadj_xy
      have : x ∈ G.neighborFinset v2 := by
        rw [G.mem_neighborFinset]
        exact hadj_xv2.symm
      rw [h_Nv2_eq, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with (rfl | rfl)
      · exact hxu rfl
      · exact hxv1 rfl
  refine ⟨u, fun v hv => ?_⟩
  rcases h_all_mem v with (rfl | rfl | rfl)
  · exact (hv rfl).elim
  · exact hadj_uv1
  · exact hadj_uv2

end FriendshipTheorem
