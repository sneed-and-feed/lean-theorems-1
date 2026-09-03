import Formalization.FriendshipTheorem.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Vertex Degrees and Universal Vertices (The Politician Lemma)

This module establishes the degree properties of vertices in a friendship graph:
1. **Degree Equality for Non-Adjacent Vertices**: If $u \not\sim v$, then $\deg(u) = \deg(v)$.
2. **Universal Vertex from Degree Inequality**: If the graph is not regular, there exists
   a vertex $w$ of strictly maximal degree that is universal ($\deg(w) = |V| - 1$).
3. **Even Degree Parity**: In every friendship graph, every vertex degree is even.
4. **Order Formula**: In a $k$-regular friendship graph, $|V| = k(k-1) + 1$.

## Main Theorems
* `degree_eq_of_not_adj`: Non-adjacent vertices have equal degree.
* `adj_of_degree_ne`: Distinct vertices with unequal degree must be adjacent.
* `exists_universal_of_exists_degree_ne`: If there exist two vertices of different degree,
  there exists a universal vertex.
* `even_degree_of_friendship`: The degree of every vertex is even.
* `card_V_eq_k_mul_k_sub_one_add_one`: In any $k$-regular friendship graph on $\ge 3$ vertices,
  $|V| = k(k - 1) + 1$.
-/

namespace FriendshipTheorem

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

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
  by_contra h; push Not at h; rcases h with ⟨hxa, hxb, hadja, hadjb⟩
  exact h_deg_ne <| (degree_eq_of_not_adj h_friend hxa.symm hadja).trans
    (degree_eq_of_not_adj h_friend hxb.symm hadjb).symm

lemma neighbor_diff_deg_eq (h_friend : HasFriendshipProperty G) {a b : V}
    (hab : G.Adj a b) (_h_deg_ne : G.degree a ≠ G.degree b)
    {x : V} (hx : x ∈ G.neighborFinset a)
    (hxb : x ≠ b) (hxc : x ≠ commonNeighbor h_friend hab.ne) :
    G.degree x = G.degree b := by
  apply degree_eq_of_not_adj h_friend hxb
  intro hxb_adj
  apply hxc <| commonNeighbor_eq_of_mem h_friend hab.ne _
  rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
  exact ⟨by rwa [G.mem_neighborFinset] at hx, hxb_adj.symm⟩

lemma degree_ge_two_of_adj (h_friend : HasFriendshipProperty G) {a b : V} (hab : G.Adj a b) :
    2 ≤ G.degree b := by
  let c := commonNeighbor h_friend hab.ne
  have h_sub : {a, c} ⊆ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [G.mem_neighborFinset]
      exact hab.symm
    · rw [G.mem_neighborFinset]
      exact commonNeighbor_adj_right h_friend hab.ne
  have := Finset.card_le_card h_sub
  rwa [Finset.card_pair (commonNeighbor_adj_left h_friend hab.ne).ne] at this

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
    dsimp [f]; rw [dite_eq_left hx]
  have hf_mem : ∀ x ∈ G.neighborFinset u, f x ∈ G.neighborFinset u := by
    intro x hx
    rw [hf_def hx]
    exact (Finset.mem_inter.mp (commonNeighbor_mem_inter h_friend (h_ne_of_mem hx))).1
  have hf_ne : ∀ x ∈ G.neighborFinset u, f x ≠ x := by
    intro x hx
    rw [hf_def hx]
    exact (commonNeighbor_adj_right h_friend (h_ne_of_mem hx)).ne.symm
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
    exact (commonNeighbor_eq_of_mem h_friend (h_ne_of_mem hfx_in) hx_mem_inter).symm
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
    · rw [ite_eq_left hu]
      have h_sd := Finset.sum_sdiff (Finset.subset_univ s)
        (f := fun v => if P u v ∧ u ∈ s ∧ v ∈ s then (1 : ℕ) else 0)
      have h_zero : ∑ v ∈ Finset.univ \ s, (if P u v ∧ u ∈ s ∧ v ∈ s then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rw [Finset.mem_sdiff] at hv
        rw [ite_eq_right (by rintro ⟨-, -, hvs⟩; exact hv.2 hvs)]
      rw [h_zero, zero_add] at h_sd
      rw [← h_sd]
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hP : P u v
      · rw [ite_eq_left ⟨hP, hu, hv⟩, ite_eq_left hP]
      · rw [ite_eq_right (by rintro ⟨h1, -⟩; exact hP h1), ite_eq_right hP]
    · rw [ite_eq_right hu]
      apply Finset.sum_eq_zero
      intro v _
      rw [ite_eq_right (by rintro ⟨-, hus, -⟩; exact hu hus)]
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
    rw [ite_eq_right hu.2]
  rw [h_zero, zero_add] at h_sd
  rw [← h_sd]
  apply Finset.sum_congr rfl
  intro u hu
  rw [ite_eq_left hu]

omit [Fintype V] in
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

omit [Fintype V] in
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
        rw [ite_eq_right (by intro h; exact h rfl)]
        rw [Finset.sum_eq_zero]
        intro w _
        rw [ite_eq_right]
        rintro ⟨h1, -⟩
        exact h1 rfl
      · rw [ite_eq_left huv]
        apply Finset.sum_congr rfl
        intro w _
        by_cases hw : u ∈ G.neighborFinset w ∧ v ∈ G.neighborFinset w
        · rw [ite_eq_left hw, ite_eq_left ⟨huv, hw⟩]
        · rw [ite_eq_right hw, ite_eq_right (by rintro ⟨-, h2⟩; exact hw h2)]
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

end FriendshipTheorem
