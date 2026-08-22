import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# The Friendship Theorem (Erdős–Rényi–Sós, 1966)

This module formalizes the **Friendship Theorem**
(P. Erdős, A. Rényi, V. T. Sós, 1966).

## Mathematical Statement
Let $G = (V, E)$ be a finite simple graph such that every pair of distinct vertices has
*exactly one* common neighbor:
$$\forall u \ne v \in V, \quad |N(u) \cap N(v)| = 1$$

Then there exists a universal vertex $w \in V$ connected to all other vertices
($\deg(w) = |V| - 1$), and the graph $G$ consists of a set of triangles sharing the single
universal vertex $w$ (a "windmill graph" or "friendship graph" $Wd(k, 2)$).

## References
* P. Erdős, A. Rényi, V. T. Sós (1966), *On a problem of graph theory*, Studia Sci. Math. Hungar., 1:215–235.
* H. S. Wilf (1971), *The friendship theorem*, in *Combinatorial Mathematics and its Applications*, Academic Press.
-/

namespace FriendshipTheorem

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (or "politician") in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The unique common neighbor of two distinct vertices in a friendship graph. -/
noncomputable def commonNeighbor (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) : V :=
  Finset.card_eq_one.mp (h_friend u v huv) |>.choose

lemma commonNeighbor_mem_inter (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv ∈ G.neighborFinset u ∩ G.neighborFinset v := by
  have h := Finset.card_eq_one.mp (h_friend u v huv) |>.choose_spec
  rw [h]
  exact Finset.mem_singleton_self _

lemma inter_eq_singleton_commonNeighbor (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    G.neighborFinset u ∩ G.neighborFinset v = {commonNeighbor h_friend huv} :=
  Finset.card_eq_one.mp (h_friend u v huv) |>.choose_spec

lemma commonNeighbor_adj_left (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    G.Adj u (commonNeighbor h_friend huv) := by
  have h := commonNeighbor_mem_inter h_friend huv
  rw [Finset.mem_inter, G.mem_neighborFinset] at h
  exact h.1

lemma commonNeighbor_adj_right (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    G.Adj v (commonNeighbor h_friend huv) := by
  have h := commonNeighbor_mem_inter h_friend huv
  rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at h
  exact h.2

lemma commonNeighbor_symm (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv = commonNeighbor h_friend huv.symm := by
  have h1 : commonNeighbor h_friend huv ∈ G.neighborFinset v ∩ G.neighborFinset u := by
    rw [Finset.inter_comm]
    exact commonNeighbor_mem_inter h_friend huv
  have h2 := inter_eq_singleton_commonNeighbor h_friend huv.symm
  rw [h2, Finset.mem_singleton] at h1
  exact h1

lemma commonNeighbor_eq_of_mem (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v)
    {w : V} (hw : w ∈ G.neighborFinset u ∩ G.neighborFinset v) :
    w = commonNeighbor h_friend huv := by
  have h := inter_eq_singleton_commonNeighbor h_friend huv
  rw [h, Finset.mem_singleton] at hw
  exact hw

lemma commonNeighbor_ne_left (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv ≠ u := by
  have hadj := commonNeighbor_adj_left h_friend huv
  exact hadj.ne.symm

lemma commonNeighbor_ne_right (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv ≠ v := by
  have hadj := commonNeighbor_adj_right h_friend huv
  exact hadj.ne.symm

/-- **Equal Degrees for Non-Adjacent Vertices:**
In a graph with the friendship property, any two distinct non-adjacent vertices have the same degree. -/
theorem degree_eq_of_not_adj (h_friend : HasFriendshipProperty G) {u v : V}
    (huv : u ≠ v) (h_not_adj : ¬ G.Adj u v) :
    G.degree u = G.degree v := by
  have h_deg (x : V) : G.degree x = (G.neighborFinset x).card := rfl
  rw [h_deg u, h_deg v]
  have h_ne_v {x : V} (hx : x ∈ G.neighborFinset u) : x ≠ v := by
    rintro rfl
    rw [G.mem_neighborFinset] at hx
    exact h_not_adj hx
  have h_ne_u {y : V} (hy : y ∈ G.neighborFinset v) : y ≠ u := by
    rintro rfl
    rw [G.mem_neighborFinset] at hy
    exact h_not_adj hy.symm
  refine Finset.card_bij (fun x hx => commonNeighbor h_friend (h_ne_v hx)) ?_ ?_ ?_
  · intro x hx
    have hmem := commonNeighbor_mem_inter h_friend (h_ne_v hx)
    rw [Finset.mem_inter] at hmem
    exact hmem.2
  · intro x1 hx1 x2 hx2 heq
    have h_ne_v1 := h_ne_v hx1
    have h_ne_v2 := h_ne_v hx2
    let y := commonNeighbor h_friend h_ne_v1
    have hy_eq : y = commonNeighbor h_friend h_ne_v2 := heq
    have hy_adj_v : G.Adj v y := commonNeighbor_adj_right h_friend h_ne_v1
    have hy_ne_u : u ≠ y := by
      intro h
      have : G.Adj v u := h ▸ hy_adj_v
      exact h_not_adj this.symm
    have hx1_mem : x1 ∈ G.neighborFinset u ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      refine ⟨by rwa [G.mem_neighborFinset] at hx1, ?_⟩
      have := commonNeighbor_adj_left h_friend h_ne_v1
      exact this.symm
    have hx2_mem : x2 ∈ G.neighborFinset u ∩ G.neighborFinset y := by
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      refine ⟨by rwa [G.mem_neighborFinset] at hx2, ?_⟩
      have := commonNeighbor_adj_left h_friend h_ne_v2
      rw [← hy_eq] at this
      exact this.symm
    have hx1_eq := commonNeighbor_eq_of_mem h_friend hy_ne_u hx1_mem
    have hx2_eq := commonNeighbor_eq_of_mem h_friend hy_ne_u hx2_mem
    exact hx1_eq.trans hx2_eq.symm
  · intro y hy
    have hy_ne := h_ne_u hy
    have hu_ne_y : u ≠ y := hy_ne.symm
    let x := commonNeighbor h_friend hu_ne_y
    have hx_mem_u : x ∈ G.neighborFinset u := by
      have hmem := commonNeighbor_mem_inter h_friend hu_ne_y
      rw [Finset.mem_inter] at hmem
      exact hmem.1
    refine ⟨x, hx_mem_u, ?_⟩
    have hx_ne_v := h_ne_v hx_mem_u
    have hy_mem : y ∈ G.neighborFinset x ∩ G.neighborFinset v := by
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      refine ⟨?_, by rwa [G.mem_neighborFinset] at hy⟩
      have := commonNeighbor_adj_right h_friend hu_ne_y
      exact this.symm
    exact (commonNeighbor_eq_of_mem h_friend hx_ne_v hy_mem).symm

lemma adj_of_degree_ne (h_friend : HasFriendshipProperty G) {u v : V}
    (huv : u ≠ v) (h_deg_ne : G.degree u ≠ G.degree v) :
    G.Adj u v := by
  by_contra h_not
  exact h_deg_ne (degree_eq_of_not_adj h_friend huv h_not)

lemma adj_or_eq_of_degree_ne (h_friend : HasFriendshipProperty G) {a b : V}
    (h_deg_ne : G.degree a ≠ G.degree b) (x : V) :
    x = a ∨ x = b ∨ G.Adj a x ∨ G.Adj b x := by
  by_cases hxa : x = a
  · exact Or.inl hxa
  · by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    · by_cases h_adja : G.Adj a x
      · exact Or.inr (Or.inr (Or.inl h_adja))
      · by_cases h_adjb : G.Adj b x
        · exact Or.inr (Or.inr (Or.inr h_adjb))
        · have h1 := degree_eq_of_not_adj h_friend (Ne.symm hxa) h_adja
          have h2 := degree_eq_of_not_adj h_friend (Ne.symm hxb) h_adjb
          rw [h1, ← h2] at h_deg_ne
          exact (h_deg_ne rfl).elim

lemma neighbor_diff_deg_eq (h_friend : HasFriendshipProperty G) {a b : V}
    (hab : G.Adj a b) (_h_deg_ne : G.degree a ≠ G.degree b)
    {x : V} (hx : x ∈ G.neighborFinset a)
    (hxb : x ≠ b) (hxc : x ≠ commonNeighbor h_friend hab.ne) :
    G.degree x = G.degree b := by
  have hxa : G.Adj a x := by rwa [G.mem_neighborFinset] at hx
  have hx_ne_a : x ≠ a := hxa.ne.symm
  have h_not_xb : ¬ G.Adj x b := by
    intro hxb_adj
    have hx_mem_inter : x ∈ G.neighborFinset a ∩ G.neighborFinset b := by
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      exact ⟨hxa, hxb_adj.symm⟩
    have hx_eq_c := commonNeighbor_eq_of_mem h_friend hab.ne hx_mem_inter
    exact hxc hx_eq_c
  have h_ne_xb : x ≠ b := hxb
  exact degree_eq_of_not_adj h_friend h_ne_xb h_not_xb

lemma degree_ge_two_of_adj (h_friend : HasFriendshipProperty G) {a b : V} (hab : G.Adj a b) :
    2 ≤ G.degree b := by
  let c := commonNeighbor h_friend hab.ne
  have hac : G.Adj a c := commonNeighbor_adj_left h_friend hab.ne
  have hbc : G.Adj b c := commonNeighbor_adj_right h_friend hab.ne
  have h_ac_ne : a ≠ c := hac.ne
  have h_sub : {a, c} ⊆ G.neighborFinset b := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl)
    · rw [G.mem_neighborFinset]
      exact hab.symm
    · rw [G.mem_neighborFinset]
      exact hbc
  have h_card_pair : ({a, c} : Finset V).card = 2 := Finset.card_pair h_ac_ne
  have h_le := Finset.card_le_card h_sub
  rw [h_card_pair] at h_le
  exact h_le

/-- In a friendship graph, if there are two vertices of different degrees, the vertex with
strictly larger degree is universal (connected to all other vertices). -/
lemma exists_universal_of_degree_ne (h_friend : HasFriendshipProperty G) {a b : V}
    (hab : G.Adj a b) (h_deg_lt : G.degree b < G.degree a) :
    IsUniversalVertex G a := by
  intro v hva
  by_contra h_not_adj
  have h_not_adj_va : ¬ G.Adj v a := fun h => h_not_adj h.symm
  have h_deg_v : G.degree v = G.degree a := degree_eq_of_not_adj h_friend hva h_not_adj_va
  have h_deg_vb : G.degree v ≠ G.degree b := by omega
  have hv_ne_b : v ≠ b := by
    rintro rfl
    exact h_deg_vb (h_deg_v.symm ▸ rfl)
  have hadj_vb : G.Adj v b := adj_of_degree_ne h_friend hv_ne_b h_deg_vb
  have h_deg_b_ge2 : 2 ≤ G.degree b := degree_ge_two_of_adj h_friend hab
  have _h_deg_a_ge3 : 3 ≤ G.degree a := by omega
  let c := commonNeighbor h_friend hab.ne
  have hc_in : c ∈ G.neighborFinset a := by
    have := commonNeighbor_mem_inter h_friend hab.ne
    rw [Finset.mem_inter] at this
    exact this.1
  have hb_in : b ∈ G.neighborFinset a := by
    rw [G.mem_neighborFinset]
    exact hab
  have hbc_ne : b ≠ c := (commonNeighbor_ne_right h_friend hab.ne).symm
  have h_pair_sub : ({b, c} : Finset V) ⊆ G.neighborFinset a := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with (rfl | rfl) <;> assumption
  have h_pair_card : ({b, c} : Finset V).card = 2 := Finset.card_pair hbc_ne
  have h_sdiff_card : (G.neighborFinset a \ {b, c}).card = G.degree a - 2 := by
    rw [Finset.card_sdiff_of_subset h_pair_sub, h_pair_card]
    rfl
  have h_sdiff_pos : 0 < (G.neighborFinset a \ {b, c}).card := by
    rw [h_sdiff_card]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h_sdiff_pos
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  have hx_in_a : x ∈ G.neighborFinset a := hx.1
  have hxb : x ≠ b := hx.2.1
  have hxc : x ≠ c := hx.2.2
  have h_deg_x : G.degree x = G.degree b :=
    neighbor_diff_deg_eq h_friend hab (by omega) hx_in_a hxb hxc
  have h_deg_vx : G.degree v ≠ G.degree x := by
    rw [h_deg_x]
    exact h_deg_vb
  have hv_ne_x : v ≠ x := by
    rintro rfl
    exact h_deg_vx rfl
  have hadj_vx : G.Adj v x := adj_of_degree_ne h_friend hv_ne_x h_deg_vx
  have hb_inter : b ∈ G.neighborFinset a ∩ G.neighborFinset v := by
    rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
    exact ⟨hab, hadj_vb⟩
  have hx_inter : x ∈ G.neighborFinset a ∩ G.neighborFinset v := by
    rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
    exact ⟨by rwa [G.mem_neighborFinset] at hx_in_a, hadj_vx⟩
  have h_sub_inter : ({b, x} : Finset V) ⊆ G.neighborFinset a ∩ G.neighborFinset v := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with (rfl | rfl) <;> assumption
  have h_card_bx : ({b, x} : Finset V).card = 2 := Finset.card_pair hxb.symm
  have h_le := Finset.card_le_card h_sub_inter
  rw [h_card_bx] at h_le
  have h_card_inter := h_friend a v (Ne.symm hva)
  rw [h_card_inter] at h_le
  omega

lemma exists_universal_of_exists_degree_ne (h_friend : HasFriendshipProperty G)
    (h_nonreg : ∃ a b : V, G.degree a ≠ G.degree b) :
    ∃ w : V, IsUniversalVertex G w := by
  obtain ⟨a, b, h_ne⟩ := h_nonreg
  rcases lt_or_gt_of_ne h_ne with (hlt | hgt)
  · have hab : G.Adj b a := adj_of_degree_ne h_friend (by rintro rfl; exact hlt.ne rfl) (by omega)
    exact ⟨b, exists_universal_of_degree_ne h_friend hab hlt⟩
  · have hab : G.Adj a b := adj_of_degree_ne h_friend (by rintro rfl; exact hgt.ne rfl) (by omega)
    exact ⟨a, exists_universal_of_degree_ne h_friend hab hgt⟩

lemma even_card_of_involution {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → α) (hf_mem : ∀ x ∈ s, f x ∈ s)
    (hf_ne : ∀ x ∈ s, f x ≠ x) (hf_invol : ∀ x ∈ s, f (f x) = x) :
    Even s.card := by
  generalize hn : s.card = n
  induction' n using Nat.strong_induction_on with n ih generalizing s
  by_cases hn0 : n = 0
  · subst hn0
    exact ⟨0, rfl⟩
  · have h_pos : 0 < s.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp h_pos
    let y := f x
    have hy : y ∈ s := hf_mem x hx
    have hne : x ≠ y := (hf_ne x hx).symm
    let s' := s \ {x, y}
    have h_sub : {x, y} ⊆ s := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with (rfl | rfl) <;> assumption
    have h_pair_card : ({x, y} : Finset α).card = 2 := Finset.card_pair hne
    have hs'_card : s'.card = s.card - 2 := by
      dsimp [s']
      rw [Finset.card_sdiff_of_subset h_sub, h_pair_card]
    have hs'_lt : s'.card < n := by omega
    have hf_mem' : ∀ z ∈ s', f z ∈ s' := by
      intro z hz
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      have hfz_in : f z ∈ s := hf_mem z hz.1
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hfz_in, ?_, ?_⟩
      · intro h_eq
        have : f (f z) = f x := by rw [h_eq]
        rw [hf_invol z hz.1] at this
        exact hz.2.2 this
      · intro h_eq
        have : f (f z) = f y := by rw [h_eq]
        rw [hf_invol z hz.1] at this
        have hfy : f y = x := hf_invol x hx
        rw [hfy] at this
        exact hz.2.1 this
    have hf_ne' : ∀ z ∈ s', f z ≠ z := by
      intro z hz
      have hz_in : z ∈ s := (Finset.mem_sdiff.mp hz).1
      exact hf_ne z hz_in
    have hf_invol' : ∀ z ∈ s', f (f z) = z := by
      intro z hz
      have hz_in : z ∈ s := (Finset.mem_sdiff.mp hz).1
      exact hf_invol z hz_in
    have h_even_s' := ih s'.card hs'_lt s' hf_mem' hf_ne' hf_invol' rfl
    obtain ⟨k, hk⟩ := h_even_s'
    have h_n_eq : n = s'.card + 2 := by
      rw [hs'_card, hn]
      have : 2 ≤ s.card := by
        have : ({x, y} : Finset α).card ≤ s.card := Finset.card_le_card h_sub
        rwa [h_pair_card] at this
      omega
    rw [h_n_eq, hk]
    exact ⟨k + 1, by omega⟩

lemma even_degree_of_friendship (h_friend : HasFriendshipProperty G) (u : V) :
    Even (G.degree u) := by
  have h_ne_of_mem {x : V} (hx : x ∈ G.neighborFinset u) : u ≠ x := by
    rw [G.mem_neighborFinset] at hx; exact hx.ne
  let f (x : V) : V :=
    if hx : x ∈ G.neighborFinset u then
      commonNeighbor h_friend (h_ne_of_mem hx)
    else x
  have hf_def {x : V} (hx : x ∈ G.neighborFinset u) : f x = commonNeighbor h_friend (h_ne_of_mem hx) := by
    dsimp [f]; rw [dif_pos hx]
  have hf_mem : ∀ x ∈ G.neighborFinset u, f x ∈ G.neighborFinset u := by
    intro x hx
    rw [hf_def hx]
    have := commonNeighbor_mem_inter h_friend (h_ne_of_mem hx)
    rw [Finset.mem_inter] at this
    exact this.1
  have hf_ne : ∀ x ∈ G.neighborFinset u, f x ≠ x := by
    intro x hx
    rw [hf_def hx]
    have := commonNeighbor_adj_right h_friend (h_ne_of_mem hx)
    exact this.ne.symm
  have hf_invol : ∀ x ∈ G.neighborFinset u, f (f x) = x := by
    intro x hx
    have hfx_in := hf_mem x hx
    have hf_def_fx : f (f x) = commonNeighbor h_friend (h_ne_of_mem hfx_in) := hf_def hfx_in
    have hf_def_x : f x = commonNeighbor h_friend (h_ne_of_mem hx) := hf_def hx
    rw [hf_def_fx]
    have hadj_xy : G.Adj x (f x) := by
      have := commonNeighbor_adj_right h_friend (h_ne_of_mem hx)
      rwa [← hf_def_x] at this
    have hx_mem_inter : x ∈ G.neighborFinset u ∩ G.neighborFinset (f x) := by
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      have : G.Adj u x := by rwa [G.mem_neighborFinset] at hx
      exact ⟨this, hadj_xy.symm⟩
    have h_eq := commonNeighbor_eq_of_mem h_friend (h_ne_of_mem hfx_in) hx_mem_inter
    exact h_eq.symm
  have h_deg : G.degree u = (G.neighborFinset u).card := rfl
  rw [h_deg]
  exact even_card_of_involution (G.neighborFinset u) f hf_mem hf_ne hf_invol

lemma sum3_comm {α : Type*} [Fintype α] (f : α → α → α → ℕ) :
    (∑ u : α, ∑ v : α, ∑ w : α, f u v w) = ∑ w : α, ∑ u : α, ∑ v : α, f u v w := by
  have h1 : (∑ u : α, ∑ v : α, ∑ w : α, f u v w) = ∑ u : α, ∑ w : α, ∑ v : α, f u v w := by
    apply Finset.sum_congr rfl
    intro u _
    exact Finset.sum_comm
  rw [h1, Finset.sum_comm]

lemma sum_double_restrict (s : Finset V) (P : V → V → Prop) [DecidableRel P] :
    (∑ u : V, ∑ v : V, (if P u v ∧ u ∈ s ∧ v ∈ s then (1 : ℕ) else 0)) =
    ∑ u ∈ s, ∑ v ∈ s, (if P u v then (1 : ℕ) else 0) := by
  have h_inner (u : V) :
      (∑ v : V, if P u v ∧ u ∈ s ∧ v ∈ s then (1 : ℕ) else 0) =
      if u ∈ s then (∑ v ∈ s, if P u v then (1 : ℕ) else 0) else 0 := by
    by_cases hu : u ∈ s
    · rw [if_pos hu]
      have h_sd := Finset.sum_sdiff (Finset.subset_univ s)
        (f := fun v => if P u v ∧ u ∈ s ∧ v ∈ s then (1 : ℕ) else 0)
      have h_zero : ∑ v ∈ Finset.univ \ s, (if P u v ∧ u ∈ s ∧ v ∈ s then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [Finset.mem_sdiff] at hv
        rw [if_neg (by rintro ⟨-, -, hvs⟩; exact hv.2 hvs)]
      rw [h_zero, zero_add] at h_sd
      rw [← h_sd]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hP : P u v
      · rw [if_pos ⟨hP, hu, hv⟩, if_pos hP]
      · rw [if_neg (by rintro ⟨h1, -⟩; exact hP h1), if_neg hP]
    · rw [if_neg hu]
      apply Finset.sum_eq_zero
      intro v _
      rw [if_neg (by rintro ⟨-, hus, -⟩; exact hu hus)]
  have : (∑ u : V, ∑ v : V, if P u v ∧ u ∈ s ∧ v ∈ s then (1 : ℕ) else 0) =
      ∑ u : V, (if u ∈ s then (∑ v ∈ s, if P u v then (1 : ℕ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro u _
    exact h_inner u
  rw [this]
  have h_sd := Finset.sum_sdiff (Finset.subset_univ s)
    (f := fun u => if u ∈ s then (∑ v ∈ s, if P u v then (1 : ℕ) else 0) else 0)
  have h_zero : ∑ u ∈ Finset.univ \ s, (if u ∈ s then (∑ v ∈ s, if P u v then (1 : ℕ) else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.mem_sdiff] at hu
    rw [if_neg hu.2]
  rw [h_zero, zero_add] at h_sd
  rw [← h_sd]
  apply Finset.sum_congr rfl
  intro u hu
  rw [if_pos hu]

lemma sum_ite_ne (s : Finset V) (u : V) (hu : u ∈ s) :
    (∑ v ∈ s, (if u ≠ v then (1 : ℕ) else 0)) = s.card - 1 := by
  have h_eq : (s.filter (fun v => u ≠ v)) = s \ {u} := by
    ext v; simp [ne_comm]
  have h_card : (s.filter (fun v => u ≠ v)).card = s.card - 1 := by
    rw [h_eq, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hu), Finset.card_singleton]
  have : (∑ v ∈ s, (if u ≠ v then (1 : ℕ) else 0)) = (s.filter (fun v => u ≠ v)).card := by
    rw [Finset.sum_ite]
    simp
  rw [this, h_card]

lemma sum_pairs_ne (s : Finset V) :
    (∑ u ∈ s, ∑ v ∈ s, (if u ≠ v then (1 : ℕ) else 0)) = s.card * (s.card - 1) := by
  have : (∑ u ∈ s, ∑ v ∈ s, (if u ≠ v then (1 : ℕ) else 0)) = ∑ u ∈ s, (s.card - 1) := by
    apply Finset.sum_congr rfl
    intro u hu
    exact sum_ite_ne s u hu
  rw [this, Finset.sum_const]
  rfl

lemma card_V_eq_k_mul_k_sub_one_add_one (h_friend : HasFriendshipProperty G)
    (k : ℕ) (h_reg : ∀ v : V, G.degree v = k) (h_card : 3 ≤ Fintype.card V) :
    Fintype.card V = k * (k - 1) + 1 := by
  let n := Fintype.card V
  have hn_pos : 0 < n := by omega
  have h_sum1 : (∑ u : V, ∑ v : V, (if u ≠ v then (G.neighborFinset u ∩ G.neighborFinset v).card else 0)) =
      n * (n - 1) := by
    have h_inner (u : V) : (∑ v : V, (if u ≠ v then (G.neighborFinset u ∩ G.neighborFinset v).card else 0)) =
        n - 1 := by
      have : (∑ v : V, (if u ≠ v then (G.neighborFinset u ∩ G.neighborFinset v).card else 0)) =
          ∑ v : V, (if u ≠ v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        split_ifs with huv
        · exact h_friend u v huv
        · rfl
      rw [this]
      have h_univ : (∑ v : V, (if u ≠ v then 1 else 0)) = (∑ v ∈ (Finset.univ : Finset V), if u ≠ v then 1 else 0) := rfl
      rw [h_univ, sum_ite_ne Finset.univ u (Finset.mem_univ u), Finset.card_univ]
    have : (∑ u : V, ∑ v : V, (if u ≠ v then (G.neighborFinset u ∩ G.neighborFinset v).card else 0)) =
        ∑ u : V, (n - 1) := by
      apply Finset.sum_congr rfl
      intro u _
      exact h_inner u
    rw [this, Finset.sum_const]
    rfl
  have h_sum2 : (∑ u : V, ∑ v : V, (if u ≠ v then (G.neighborFinset u ∩ G.neighborFinset v).card else 0)) =
      n * (k * (k - 1)) := by
    have h_inter (u v : V) : (G.neighborFinset u ∩ G.neighborFinset v).card =
        ∑ w : V, (if u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w then (1 : ℕ) else 0) := by
      have : (G.neighborFinset u ∩ G.neighborFinset v).card =
          ((Finset.univ : Finset V).filter (fun w => u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w)).card := by
        congr 1
        ext w
        simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [G.adj_comm (u := u), G.adj_comm (u := v)]
      rw [this, Finset.sum_ite]
      simp
    have h_step : (∑ u : V, ∑ v : V, (if u ≠ v then (G.neighborFinset u ∩ G.neighborFinset v).card else 0)) =
        ∑ u : V, ∑ v : V, ∑ w : V, (if u ≠ v ∧ u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w then (1 : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      rw [h_inter u v]
      by_cases huv : u = v
      · subst huv
        rw [if_neg (by intro h; exact h rfl)]
        rw [Finset.sum_eq_zero]
        intro w _
        rw [if_neg]
        rintro ⟨h1, -⟩
        exact h1 rfl
      · rw [if_pos huv]
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w
        · rw [if_pos hw, if_pos ⟨huv, hw⟩]
        · rw [if_neg hw, if_neg (by rintro ⟨-, h2⟩; exact hw h2)]
    rw [h_step, sum3_comm]
    have h_w (w : V) : (∑ u : V, ∑ v : V, (if u ≠ v ∧ u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w then (1 : ℕ) else 0)) =
        k * (k - 1) := by
      rw [sum_double_restrict (G.neighborFinset w) (fun u v => u ≠ v), sum_pairs_ne]
      have : (G.neighborFinset w).card = k := h_reg w
      rw [this]
    have : (∑ w : V, ∑ u : V, ∑ v : V, (if u ≠ v ∧ u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w then (1 : ℕ) else 0)) =
        ∑ w : V, (k * (k - 1)) := by
      apply Finset.sum_congr rfl
      intro w _
      exact h_w w
    rw [this, Finset.sum_const]
    rfl
  have h_eq : n * (n - 1) = n * (k * (k - 1)) := by rw [← h_sum1, h_sum2]
  have h_n_sub1 : n - 1 = k * (k - 1) := Nat.eq_of_mul_eq_mul_left hn_pos h_eq
  omega

/-- The number of walks of length `m` from `u` to `v` in `G`. -/
def walkCount (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ → ℕ
  | 0 => if u = v then 1 else 0
  | m + 1 => ∑ x ∈ G.neighborFinset u, walkCount G x v m

lemma walkCount_one (u v : V) :
    walkCount G u v 1 = if v ∈ G.neighborFinset u then (1 : ℕ) else 0 := by
  dsimp [walkCount]
  by_cases hv : v ∈ G.neighborFinset u
  · have : ∑ x ∈ G.neighborFinset u, (if x = v then (1 : ℕ) else 0) = 1 := by
      rw [Finset.sum_ite_eq' _ v]
      rw [if_pos hv]
    rw [this, if_pos hv]
  · have : ∑ x ∈ G.neighborFinset u, (if x = v then (1 : ℕ) else 0) = 0 := by
      rw [Finset.sum_ite_eq' _ v]
      rw [if_neg hv]
    rw [this, if_neg hv]

lemma walkCount_two (h_friend : HasFriendshipProperty G) (k : ℕ)
    (h_reg : ∀ v : V, G.degree v = k) (u v : V) :
    walkCount G u v 2 = if u = v then k else 1 := by
  dsimp [walkCount]
  have h1 (x : V) : walkCount G x v 1 = if x ∈ G.neighborFinset v then (1 : ℕ) else 0 := by
    rw [walkCount_one]
    by_cases hxv : v ∈ G.neighborFinset x
    · rw [if_pos hxv]
      rw [G.mem_neighborFinset] at hxv
      have : x ∈ G.neighborFinset v := by rwa [G.mem_neighborFinset, G.adj_comm]
      rw [if_pos this]
    · rw [if_neg hxv]
      have : x ∉ G.neighborFinset v := by
        intro h
        rw [G.mem_neighborFinset, G.adj_comm] at h
        exact hxv (by rwa [G.mem_neighborFinset])
      rw [if_neg this]
  have h2 : (∑ x ∈ G.neighborFinset u, walkCount G x v 1) =
      ∑ x ∈ G.neighborFinset u, if x ∈ G.neighborFinset v then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    exact h1 x
  show (∑ x ∈ G.neighborFinset u, walkCount G x v 1) = if u = v then k else 1
  rw [h2]
  have h3 : (∑ x ∈ G.neighborFinset u, if x ∈ G.neighborFinset v then (1 : ℕ) else 0) =
      (G.neighborFinset u ∩ G.neighborFinset v).card := by
    rw [Finset.sum_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
    rfl
  rw [h3]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, Finset.inter_self, show (G.neighborFinset u).card = k from h_reg u]
  · rw [if_neg huv, h_friend u v huv]

lemma walkCount_zmod (h_friend : HasFriendshipProperty G) (k : ℕ)
    (h_reg : ∀ v : V, G.degree v = k) {p : ℕ} (hpk : (k : ZMod p) = 1)
    (m : ℕ) (hm : 2 ≤ m) (u v : V) :
    (walkCount G u v m : ZMod p) = 1 := by
  induction' m, hm using Nat.le_induction with m hm ih generalizing u
  · rw [walkCount_two h_friend k h_reg]
    by_cases huv : u = v
    · rw [if_pos huv, hpk]
    · rw [if_neg huv]
      push_cast
      rfl
  · dsimp [walkCount]
    push_cast
    have : (∑ x ∈ G.neighborFinset u, (walkCount G x v m : ZMod p)) =
        ∑ x ∈ G.neighborFinset u, 1 := by
      apply Finset.sum_congr rfl
      intro x _
      exact ih x
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_card : (G.neighborFinset u).card = k := h_reg u
    rw [h_card, hpk]

/-- Sequence of vertices representing a walk of length `m` from `u` to `v`. -/
def WalkVec (G : SimpleGraph V) (u v : V) (m : ℕ) : Type _ :=
  { w : Fin (m + 1) → V // w 0 = u ∧ w (Fin.last m) = v ∧ ∀ j : Fin m, G.Adj (w j.castSucc) (w j.succ) }

instance (u v : V) (m : ℕ) : Fintype (WalkVec G u v m) := by
  classical exact Subtype.fintype _

def walkVecZeroEquiv (u v : V) (h : u = v) : WalkVec G u v 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨fun _ => u, rfl, h, fun j => j.elim0⟩
  left_inv := by
    rintro ⟨w, hw0, hw_last, _⟩
    apply Subtype.ext
    ext ⟨i, hi⟩
    have : i = 0 := by omega
    subst this
    exact hw0.symm
  right_inv := by
    rintro ⟨⟩
    rfl

def walkVecSuccEquiv (u v : V) (m : ℕ) :
    WalkVec G u v (m + 1) ≃ Σ (x : G.neighborFinset u), WalkVec G x.1 v m where
  toFun := fun ⟨w, hw0, hw_last, hw_adj⟩ =>
    ⟨⟨w 1, by
      rw [G.mem_neighborFinset]
      have hadj := hw_adj 0
      have h0 : (0 : Fin (m + 1)).castSucc = 0 := rfl
      have h1 : (0 : Fin (m + 1)).succ = 1 := rfl
      rw [h0, h1, hw0] at hadj
      exact hadj⟩,
     ⟨Fin.tail w,
      rfl,
      by
        show w (Fin.last m).succ = v
        have : (Fin.last m).succ = Fin.last (m + 1) := by ext; simp [Fin.last]
        rw [this, hw_last],
      fun j => by
        show G.Adj (w j.castSucc.succ) (w j.succ.succ)
        have h1 : j.castSucc.succ = (j.succ : Fin (m + 1)).castSucc := by ext; simp
        have h2 : j.succ.succ = (j.succ : Fin (m + 1)).succ := by ext; simp
        rw [h1, h2]
        exact hw_adj j.succ⟩⟩
  invFun := fun ⟨⟨x, hx⟩, ⟨p, hp0, hp_last, hp_adj⟩⟩ =>
    ⟨Fin.cons u p,
     by rw [Fin.cons_zero],
     by
       have : (Fin.last (m + 1) : Fin (m + 2)) = (Fin.last m).succ := by ext; simp [Fin.last]
       rw [this, Fin.cons_succ, hp_last],
     fun j => by
       cases j using Fin.cases with
       | zero =>
         have h0 : (0 : Fin (m + 1)).castSucc = 0 := rfl
         have h1 : (0 : Fin (m + 1)).succ = (1 : Fin (m + 2)) := rfl
         rw [h0, h1, Fin.cons_zero]
         rw [show (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ from rfl, Fin.cons_succ, hp0]
         rw [G.mem_neighborFinset] at hx
         exact hx
       | succ j' =>
         have h1 : (j'.succ : Fin (m + 1)).castSucc = j'.castSucc.succ := by ext; simp
         have h2 : (j'.succ : Fin (m + 1)).succ = j'.succ.succ := by ext; simp
         rw [h1, h2, Fin.cons_succ, Fin.cons_succ]
         exact hp_adj j'⟩
  left_inv := by
    rintro ⟨w, hw0, hw_last, hw_adj⟩
    apply Subtype.ext
    ext i
    cases i using Fin.cases with
    | zero => simp [hw0]
    | succ j => simp [Fin.tail]
  right_inv := by
    rintro ⟨x, ⟨p, hp0, hp_last, hp_adj⟩⟩
    have hx_adj : G.Adj u (p 0) := by
      have : p 0 = x.1 := hp0
      rw [this]
      have hx2 := x.2
      rw [G.mem_neighborFinset] at hx2
      exact hx2
    have hx : (⟨p 0, by rw [G.mem_neighborFinset]; exact hx_adj⟩ : G.neighborFinset u) = x := Subtype.ext hp0
    cases hx
    rfl

lemma card_walkVec (u v : V) (m : ℕ) :
    Fintype.card (WalkVec G u v m) = walkCount G u v m := by
  induction' m with m ih generalizing u
  · dsimp [walkCount]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      have : WalkVec G u u 0 ≃ Unit := walkVecZeroEquiv u u rfl
      rw [Fintype.card_congr this, Fintype.card_unit]
    · rw [if_neg huv]
      have : IsEmpty (WalkVec G u v 0) := ⟨by
        rintro ⟨w, hw0, hw_last, _⟩
        have : u = v := hw0.symm.trans hw_last
        exact huv this⟩
      exact Fintype.card_eq_zero
  · dsimp [walkCount]
    rw [Fintype.card_congr (walkVecSuccEquiv u v m)]
    rw [Fintype.card_sigma]
    have : (∑ (x : G.neighborFinset u), Fintype.card (WalkVec G x.1 v m)) =
        ∑ x ∈ G.neighborFinset u, walkCount G x v m := by
      rw [← Finset.sum_attach (G.neighborFinset u) (fun x => walkCount G x v m)]
      apply Finset.sum_congr rfl
      intro ⟨x, hx⟩ _
      exact ih x
    exact this

/-- Closed walks of length `p` in `G`. -/
def ClosedWalk (G : SimpleGraph V) (p : ℕ) [NeZero p] : Type _ :=
  { w : ZMod p → V // ∀ i : ZMod p, G.Adj (w i) (w (i + 1)) }

instance (p : ℕ) [NeZero p] : Fintype (ClosedWalk G p) := by
  classical exact Subtype.fintype _

def closedWalkShift (G : SimpleGraph V) {p : ℕ} [NeZero p] (s : ZMod p) (w : ClosedWalk G p) : ClosedWalk G p :=
  ⟨fun i => w.1 (i + s), fun i => by
    have hw := w.2 (i + s)
    have : i + s + 1 = i + 1 + s := by ring
    rw [this] at hw
    exact hw⟩

instance {p : ℕ} [NeZero p] : SMul (Multiplicative (ZMod p)) (ClosedWalk G p) where
  smul g w := closedWalkShift G (Multiplicative.toAdd g) w

instance {p : ℕ} [NeZero p] : MulAction (Multiplicative (ZMod p)) (ClosedWalk G p) where
  one_smul w := Subtype.ext (funext fun i => by
    change w.1 (i + 0) = w.1 i
    rw [add_zero])
  mul_smul g1 g2 w := Subtype.ext (funext fun i => by
    change w.1 (i + (Multiplicative.toAdd g1 + Multiplicative.toAdd g2)) = w.1 (i + Multiplicative.toAdd g1 + Multiplicative.toAdd g2)
    rw [add_assoc])

lemma closedWalk_fixedPoints_empty {p : ℕ} [Fact p.Prime] (_hp : 3 ≤ p) :
    IsEmpty (MulAction.fixedPoints (Multiplicative (ZMod p)) (ClosedWalk G p)) := by
  constructor
  intro ⟨w, hw⟩
  have h_fix : Multiplicative.ofAdd (1 : ZMod p) • w = w := hw (Multiplicative.ofAdd 1)
  have h_ext : (Multiplicative.ofAdd (1 : ZMod p) • w : ClosedWalk G p).1 = w.1 := by rw [h_fix]
  have h0 : (w.1 (0 + 1) : V) = w.1 0 := congr_fun h_ext 0
  rw [zero_add] at h0
  have hadj := w.2 0
  rw [zero_add, h0] at hadj
  exact hadj.ne rfl

lemma card_closedWalk_mod_p {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    (Fintype.card (ClosedWalk G p) : ZMod p) = 0 := by
  have h_pg : IsPGroup p (Multiplicative (ZMod p)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, pow_one]
  have h_modeq := h_pg.card_modEq_card_fixedPoints (ClosedWalk G p)
  have h_empty : IsEmpty (MulAction.fixedPoints (Multiplicative (ZMod p)) (ClosedWalk G p)) :=
    closedWalk_fixedPoints_empty hp
  have h_zero : Nat.card (MulAction.fixedPoints (Multiplicative (ZMod p)) (ClosedWalk G p)) = 0 :=
    Nat.card_eq_zero.mpr (Or.inl h_empty)
  rw [h_zero] at h_modeq
  rw [Nat.ModEq, Nat.zero_mod] at h_modeq
  have h_dvd : p ∣ Fintype.card (ClosedWalk G p) := by
    rw [Nat.card_eq_fintype_card] at h_modeq
    exact Nat.dvd_of_mod_eq_zero h_modeq
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h_dvd

def CW_at (G : SimpleGraph V) (p : ℕ) [NeZero p] (v : V) : Type _ :=
  { w : ZMod p → V // w 0 = v ∧ ∀ i : ZMod p, G.Adj (w i) (w (i + 1)) }

instance (p : ℕ) [NeZero p] (v : V) : Fintype (CW_at G p v) := by
  classical exact Subtype.fintype _

def closedWalkSigmaEquiv (p : ℕ) [NeZero p] :
    ClosedWalk G p ≃ Σ v : V, CW_at G p v where
  toFun w := ⟨w.1 0, ⟨w.1, rfl, w.2⟩⟩
  invFun := fun ⟨v, ⟨w, hw0, hw_adj⟩⟩ => ⟨w, hw_adj⟩
  left_inv := fun w => Subtype.ext rfl
  right_inv := by
    rintro ⟨v, ⟨w, rfl, hw_adj⟩⟩
    rfl

def cwAtEquivWalkVec (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (v : V) :
    CW_at G p v ≃ WalkVec G v v p where
  toFun := fun ⟨cw, hw0, hw_adj⟩ =>
    ⟨fun j => cw (j.1 : ZMod p),
     by
       have : ((0 : Fin (p + 1)).1 : ZMod p) = 0 := by simp
       show cw ((0 : Fin (p + 1)).1 : ZMod p) = v
       rw [this, hw0],
     by
       have : ((Fin.last p : Fin (p + 1)).1 : ZMod p) = 0 := by simp [Fin.last]
       show cw ((Fin.last p : Fin (p + 1)).1 : ZMod p) = v
       rw [this, hw0],
     fun j => by
       have hj_cs : (j.castSucc : Fin (p + 1)).1 = (j.1 : ℕ) := rfl
       have hj_s : ((j.succ : Fin (p + 1)).1 : ZMod p) = (j.1 : ZMod p) + 1 := by
         have : (j.succ : Fin (p + 1)).1 = j.1 + 1 := rfl
         rw [this]
         push_cast
         rfl
       have hadj := hw_adj (j.1 : ZMod p)
       show G.Adj (cw ((j.castSucc : Fin (p + 1)).1 : ZMod p)) (cw ((j.succ : Fin (p + 1)).1 : ZMod p))
       rw [hj_cs, hj_s]
       exact hadj⟩
  invFun := fun ⟨w, hw0, hw_last, hw_adj⟩ =>
    ⟨fun (i : ZMod p) => w ⟨i.val, by have := ZMod.val_lt i; omega⟩,
     by
       have h0 : (⟨(0 : ZMod p).val, by have := ZMod.val_lt (0 : ZMod p); omega⟩ : Fin (p + 1)) = 0 := by
         ext; simp [ZMod.val_zero]
       show w ⟨(0 : ZMod p).val, by have := ZMod.val_lt (0 : ZMod p); omega⟩ = v
       rw [h0, hw0],
     fun (i : ZMod p) => by
       have hp_pos : 0 < p := Nat.Prime.pos Fact.out
       by_cases hi : i.val + 1 < p
       · have h_val_add : (i + 1).val = i.val + 1 := by
           rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
         have hadj := hw_adj ⟨i.val, by omega⟩
         have h1 : (⟨i.val, by have := ZMod.val_lt i; omega⟩ : Fin (p + 1)) =
             (⟨i.val, by omega⟩ : Fin p).castSucc := rfl
         have h2 : (⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩ : Fin (p + 1)) =
             (⟨i.val, by omega⟩ : Fin p).succ := by ext; simp [h_val_add]
         show G.Adj (w ⟨i.val, by have := ZMod.val_lt i; omega⟩) (w ⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩)
         rw [h1, h2]
         exact hadj
       · have hi_eq : i.val = p - 1 := by
           have := ZMod.val_lt i
           omega
         have hp_sub : p - 1 + 1 = p := by omega
         have hi1_val : (i + 1).val = 0 := by
           rw [ZMod.val_add, ZMod.val_one, hi_eq]
           rw [hp_sub, Nat.mod_self]
         have hadj := hw_adj ⟨p - 1, by omega⟩
         have h1 : (⟨i.val, by have := ZMod.val_lt i; omega⟩ : Fin (p + 1)) =
             (⟨p - 1, by omega⟩ : Fin p).castSucc := by ext; simp [hi_eq]
         have h2 : (⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩ : Fin (p + 1)) = 0 := by
           ext; simp [hi1_val]
         have h_last : (⟨p - 1, by omega⟩ : Fin p).succ = Fin.last p := by ext; simp [Fin.last]; omega
         show G.Adj (w ⟨i.val, by have := ZMod.val_lt i; omega⟩) (w ⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩)
         rw [h1, h2, hw0]
         have h_adj' : G.Adj (w (⟨p - 1, by omega⟩ : Fin p).castSucc) (w (⟨p - 1, by omega⟩ : Fin p).succ) := hadj
         rw [h_last, hw_last] at h_adj'
         exact h_adj'⟩
  left_inv := by
    rintro ⟨cw, hw0, hw_adj⟩
    apply Subtype.ext
    ext (i : ZMod p)
    dsimp
    have : ((i.val : ℕ) : ZMod p) = i := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    exact congr_arg cw this
  right_inv := by
    rintro ⟨w, hw0, hw_last, hw_adj⟩
    apply Subtype.ext
    ext ⟨idx, hidx⟩
    dsimp
    by_cases hj_lt : idx < p
    · have : (⟨((idx : ZMod p).val : ℕ), by have := ZMod.val_lt (idx : ZMod p); omega⟩ : Fin (p + 1)) =
          ⟨idx, hidx⟩ := by
        ext
        simp [ZMod.val_natCast_of_lt hj_lt]
      rw [this]
    · have h_eq : idx = p := by omega
      have h_val_p : (((idx : ZMod p).val : ℕ) : ℕ) = 0 := by
        have : (idx : ZMod p) = (p : ZMod p) := by rw [h_eq]
        rw [this, CharP.cast_eq_zero (ZMod p) p, ZMod.val_zero]
      have h_fin_zero : (⟨((idx : ZMod p).val : ℕ), by have := ZMod.val_lt (idx : ZMod p); omega⟩ : Fin (p + 1)) = 0 := by
        ext
        exact h_val_p
      rw [h_fin_zero, hw0]
      have h_fin_last : (⟨idx, hidx⟩ : Fin (p + 1)) = Fin.last p := by
        ext
        simp [Fin.last, h_eq]
      rw [h_fin_last, hw_last]

def closedWalkEquiv (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ClosedWalk G p ≃ Σ v : V, WalkVec G v v p :=
  (closedWalkSigmaEquiv p).trans (Equiv.sigmaCongrRight (fun v => cwAtEquivWalkVec p hp v))

/-- There are no regular friendship graphs of degree `k ≥ 3`. -/
lemma no_regular_friendship_graph_ge_three (h_friend : HasFriendshipProperty G)
    (k : ℕ) (hk : 3 ≤ k) (h_reg : ∀ v : V, G.degree v = k) (h_card : 3 ≤ Fintype.card V) :
    False := by
  have h_nonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u₀⟩ := h_nonempty
  have h_even_deg := even_degree_of_friendship h_friend u₀
  rw [h_reg u₀] at h_even_deg
  have hk_even : Even k := h_even_deg
  have hk_ge4 : 4 ≤ k := by
    obtain ⟨c, hc⟩ := hk_even
    omega
  let p := (k - 1).minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ (k - 1) := Nat.minFac_dvd (k - 1)
  have hp_ge3 : 3 ≤ p := by
    have : p ≠ 2 := by
      intro hp2
      have hp2_dvd : 2 ∣ (k - 1) := hp2 ▸ hp_dvd
      obtain ⟨c, hc⟩ := hk_even
      omega
    have : 2 ≤ p := hp_prime.two_le
    omega
  have hp_fact : Fact p.Prime := ⟨hp_prime⟩
  have hpk : (k : ZMod p) = 1 := by
    have : ((k - 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (k - 1)).mpr hp_dvd
    have h_k_eq : k = (k - 1) + 1 := by omega
    rw [h_k_eq, Nat.cast_add, this, zero_add, Nat.cast_one]
  have h_card_V_zmod : (Fintype.card V : ZMod p) = 1 := by
    have h_card_V := card_V_eq_k_mul_k_sub_one_add_one h_friend k h_reg h_card
    rw [h_card_V]
    push_cast
    have : ((k - 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (k - 1)).mpr hp_dvd
    rw [this, mul_zero, zero_add]
  have h_sum_walk : (∑ v : V, (walkCount G v v p : ZMod p)) = 1 := by
    have h_each (v : V) : (walkCount G v v p : ZMod p) = 1 :=
      walkCount_zmod h_friend k h_reg hpk p (by omega) v v
    have : (∑ v : V, (walkCount G v v p : ZMod p)) = ∑ v : V, 1 := by
      apply Finset.sum_congr rfl
      intro v _
      exact h_each v
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.card : ZMod p) = (Fintype.card V : ZMod p) := rfl
    rw [this, h_card_V_zmod]
  have h_cw_zero : (Fintype.card (ClosedWalk G p) : ZMod p) = 0 :=
    card_closedWalk_mod_p hp_ge3
  have h_card_eq : Fintype.card (ClosedWalk G p) = Fintype.card (Σ v : V, WalkVec G v v p) :=
    Fintype.card_congr (closedWalkEquiv p hp_ge3)
  have h_sigma_card : Fintype.card (Σ v : V, WalkVec G v v p) = ∑ v : V, walkCount G v v p := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro v _
    exact card_walkVec v v p
  have h_cw_eq_sum : (Fintype.card (ClosedWalk G p) : ZMod p) = ∑ v : V, (walkCount G v v p : ZMod p) := by
    rw [h_card_eq, h_sigma_card]
    push_cast
    rfl
  rw [h_cw_zero, h_sum_walk] at h_cw_eq_sum
  have h_contra : (0 : ZMod p) = (1 : ZMod p) := h_cw_eq_sum
  have h_one_zero : ((1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_one]
    exact h_contra.symm
  have h_p_dvd_one : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp h_one_zero
  have : p ≤ 1 := Nat.le_of_dvd (by omega) h_p_dvd_one
  omega

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

/-- **The Friendship Theorem (Erdős–Rényi–Sós 1966):**
Any finite simple graph in which every pair of distinct vertices shares exactly one
common neighbor has a universal vertex. -/
theorem friendship_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (h_card : 3 ≤ Fintype.card V) :
    ∃ w : V, IsUniversalVertex G w := by
  by_cases h_reg_all : ∀ a b : V, G.degree a = G.degree b
  · have h_nonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨u₀⟩ := h_nonempty
    let k := G.degree u₀
    have h_reg (v : V) : G.degree v = k := h_reg_all v u₀
    rcases le_or_gt 3 k with (hk3 | hk_lt3)
    · exact (no_regular_friendship_graph_ge_three h_friend k hk3 h_reg h_card).elim
    · have hk_even := even_degree_of_friendship h_friend u₀
      have hk_even_k : Even k := hk_even
      have hk_eq_2 : k = 2 := by
        obtain ⟨c, hc⟩ := hk_even_k
        have hk_pos : 0 < k := by
          have h_deg_u : (G.neighborFinset u₀).card = k := h_reg u₀
          have : 0 < (G.neighborFinset u₀).card := by
            have : 1 < Fintype.card V := by omega
            obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp this
            have hc := commonNeighbor_mem_inter h_friend hab
            rw [Finset.mem_inter] at hc
            have hc_mem : commonNeighbor h_friend hab ∈ G.neighborFinset a := hc.1
            by_cases ha : a = u₀
            · subst ha
              exact Finset.card_pos.mpr ⟨commonNeighbor h_friend hab, hc_mem⟩
            · have hc_u := commonNeighbor_mem_inter h_friend ha
              rw [Finset.mem_inter] at hc_u
              have hc_mem_u : commonNeighbor h_friend ha ∈ G.neighborFinset u₀ := hc_u.2
              exact Finset.card_pos.mpr ⟨commonNeighbor h_friend ha, hc_mem_u⟩
          omega
        omega
      have h_reg2 (v : V) : G.degree v = 2 := by rw [h_reg v, hk_eq_2]
      exact two_regular_has_universal h_friend h_reg2 h_card
  · have h_nonreg : ∃ a b : V, G.degree a ≠ G.degree b := by
      push Not at h_reg_all
      exact h_reg_all
    exact exists_universal_of_exists_degree_ne h_friend h_nonreg

#print axioms friendship_theorem

end FriendshipTheorem
