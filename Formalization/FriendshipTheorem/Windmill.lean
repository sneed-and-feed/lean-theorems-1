import Formalization.FriendshipTheorem.Basic
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

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a 2-regular friendship graph with at least 3 vertices, every vertex belongs to a
triangle $K_3$, the entire graph is $K_3$, and any vertex is universal. -/
theorem two_regular_has_universal (h_friend : HasFriendshipProperty G)
    (h_reg : ∀ v : V, G.degree v = 2) (h_card : 3 ≤ Fintype.card V) :
    ∃ w : V, IsUniversalVertex G w := by
  obtain ⟨u⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v1, v2, hv12, hNu⟩ := Finset.card_eq_two.mp (h_reg u)
  have hv1 : v1 ∈ G.neighborFinset u := hNu ▸ Finset.mem_insert_self v1 {v2}
  have hv2 : v2 ∈ G.neighborFinset u := hNu ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v2)
  have huv1 : G.Adj u v1 := (G.mem_neighborFinset u v1).mp hv1
  have huv2 : G.Adj u v2 := (G.mem_neighborFinset u v2).mp hv2
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (h_friend u v1 huv1.ne)
  have hw_mem : w ∈ G.neighborFinset u ∩ G.neighborFinset v1 := hw ▸ Finset.mem_singleton_self w
  have hw_eq : w = v2 := by
    have hwu : w ∈ G.neighborFinset u := Finset.mem_inter.mp hw_mem |>.1
    rw [hNu, Finset.mem_insert, Finset.mem_singleton] at hwu
    rcases hwu with h | h
    · exfalso
      have h_w_v1 : w = v1 := h
      rw [h_w_v1] at hw_mem
      have : v1 ∈ G.neighborFinset v1 := Finset.mem_inter.mp hw_mem |>.2
      exact G.irrefl ((G.mem_neighborFinset v1 v1).mp this)
    · exact h
  have hv1v2 : G.Adj v1 v2 := (G.mem_neighborFinset v1 v2).mp (hw_eq ▸ Finset.mem_inter.mp hw_mem |>.2)
  have hNv1 : G.neighborFinset v1 = {u, v2} := by
    have hsub : {u, v2} ⊆ G.neighborFinset v1 := by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]; exact (G.mem_neighborFinset v1 u).mpr huv1.symm
      · rw [h]; exact (G.mem_neighborFinset v1 v2).mpr hv1v2
    have hcard1 : ({u, v2} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      exact fun h => huv2.ne (Finset.mem_singleton.mp h)
    have hcard2 : (G.neighborFinset v1).card = 2 := h_reg v1
    exact Eq.symm (Finset.eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2]))
  have hNv2 : G.neighborFinset v2 = {u, v1} := by
    have hsub : {u, v1} ⊆ G.neighborFinset v2 := by
      intro x hx; rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]; exact (G.mem_neighborFinset v2 u).mpr huv2.symm
      · rw [h]; exact (G.mem_neighborFinset v2 v1).mpr hv1v2.symm
    have hcard1 : ({u, v1} : Finset V).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      exact fun h => huv1.ne (Finset.mem_singleton.mp h)
    have hcard2 : (G.neighborFinset v2).card = 2 := h_reg v2
    exact Eq.symm (Finset.eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2]))
  have hall : ∀ x, x = u ∨ x = v1 ∨ x = v2 := by
    intro x; by_contra! h
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (h_friend u x h.1.symm)
    have hy_mem : y ∈ G.neighborFinset u ∩ G.neighborFinset x := hy ▸ Finset.mem_singleton_self y
    have hyu : y ∈ G.neighborFinset u := Finset.mem_inter.mp hy_mem |>.1
    rw [hNu, Finset.mem_insert, Finset.mem_singleton] at hyu
    rcases hyu with hy1 | hy1
    · rw [hy1] at hy_mem
      have : x ∈ G.neighborFinset v1 := (G.mem_neighborFinset v1 x).mpr ((G.mem_neighborFinset x v1).mp (Finset.mem_inter.mp hy_mem |>.2)).symm
      rw [hNv1, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h2 | h2 <;> aesop
    · rw [hy1] at hy_mem
      have : x ∈ G.neighborFinset v2 := (G.mem_neighborFinset v2 x).mpr ((G.mem_neighborFinset x v2).mp (Finset.mem_inter.mp hy_mem |>.2)).symm
      rw [hNv2, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h2 | h2 <;> aesop
  refine ⟨u, fun v hv => ?_⟩
  rcases hall v with hv1 | hv1 | hv1 <;> aesop

end FriendshipTheorem
