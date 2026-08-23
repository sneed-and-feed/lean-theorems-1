import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Formalization.FriendshipTheorem

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

namespace FriendshipWindmill

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (politician) in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

-- ============================================================================
-- Section 1: Politician Properties & Induced Matching
-- ============================================================================

/-- In a graph with the friendship property, the politician vertex `w` is adjacent to all other vertices. -/
theorem politician_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (_h_friend : HasFriendshipProperty G) (w : V)
    (h_univ : IsUniversalVertex G w) :
    G.degree w = Fintype.card V - 1 := by
  have h_nbr : G.neighborFinset w = Finset.univ.erase w := by
    ext v
    simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
    constructor
    · intro hadj
      exact hadj.ne.symm
    · intro hne
      exact h_univ v hne
  rw [degree, h_nbr, card_erase_of_mem (mem_univ w), card_univ]

/-- The induced subgraph on the non-politician vertices `V \ {w}` is 1-regular (every vertex has degree 1). -/
theorem induced_non_politician_degree_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V)
    (h_univ : IsUniversalVertex G w) (v : V) (hv : v ≠ w) :
    ((G.neighborFinset v).erase w).card = 1 := by
  have h_nbr_w : G.neighborFinset w = Finset.univ.erase w := by
    ext u
    simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
    constructor
    · intro hadj
      exact hadj.ne.symm
    · intro hne
      exact h_univ u hne
  have h_inter : G.neighborFinset v ∩ G.neighborFinset w = (G.neighborFinset v).erase w := by
    rw [h_nbr_w]
    ext u
    simp only [mem_inter, mem_erase, mem_univ, and_true]
    tauto
  rw [← h_inter]
  exact h_friend v w hv

lemma card_ne_two_of_friendship (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) :
    Fintype.card V ≠ 2 := by
  intro h_two
  have h_univ_card : (Finset.univ : Finset V).card = 2 := by
    rw [card_univ, h_two]
  obtain ⟨a, b, hab, h_univ_eq⟩ := Finset.card_eq_two.mp h_univ_card
  have hall (x : V) : x = a ∨ x = b := by
    have : x ∈ (Finset.univ : Finset V) := mem_univ x
    rw [h_univ_eq, mem_insert, mem_singleton] at this
    exact this
  have h_inter := h_friend a b hab
  have h_empty : (G.neighborFinset a ∩ G.neighborFinset b) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rw [mem_inter, mem_neighborFinset, mem_neighborFinset] at hx
    rcases hall x with (rfl | rfl)
    · exact hx.1.ne rfl
    · exact hx.2.ne rfl
  rw [h_empty, Finset.card_empty] at h_inter
  omega

lemma exists_universal_of_friendship (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) :
    ∃ w : V, IsUniversalVertex G w := by
  rcases le_or_gt 3 (Fintype.card V) with h3 | h_lt
  · exact FriendshipTheorem.friendship_theorem G h_friend h3
  · have h2 := card_ne_two_of_friendship G h_friend
    have h_pos : 0 < Fintype.card V := Fintype.card_pos
    have h_card : Fintype.card V = 1 := by omega
    have h_univ_one : (Finset.univ : Finset V).card = 1 := by rw [card_univ, h_card]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h_univ_one
    refine ⟨w, fun v hv => ?_⟩
    exfalso
    have : v ∈ (Finset.univ : Finset V) := mem_univ v
    rw [hw, mem_singleton] at this
    exact hv this

-- ============================================================================
-- Section 2: Odd Cardinality and Windmill Classification
-- ============================================================================

def windmillMatching (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) : Finset (Finset V) :=
  ((Finset.univ.erase w).powersetCard 2).filter (fun e => ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v)

lemma mem_windmillMatching_iff {G : SimpleGraph V} [DecidableRel G.Adj] {w : V} {e : Finset V} :
    e ∈ windmillMatching G w ↔ e.card = 2 ∧ (∀ x ∈ e, x ≠ w) ∧ (∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v) := by
  simp only [windmillMatching, mem_filter, mem_powersetCard, subset_erase, subset_univ, true_and]
  constructor
  · rintro ⟨⟨h_sub, h_card⟩, h_adj⟩
    refine ⟨h_card, ?_, h_adj⟩
    intro x hx
    rintro rfl
    exact h_sub hx
  · rintro ⟨h_card, h_sub, h_adj⟩
    refine ⟨⟨fun h => h_sub w h rfl, h_card⟩, h_adj⟩

lemma pair_mem_windmillMatching {G : SimpleGraph V} [DecidableRel G.Adj] {w u v : V}
    (hu : u ≠ w) (hv : v ≠ w) (hadj : G.Adj u v) :
    ({u, v} : Finset V) ∈ windmillMatching G w := by
  rw [mem_windmillMatching_iff]
  have hne := hadj.ne
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_pair hne]
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with (rfl | rfl) <;> assumption
  · refine ⟨u, mem_insert_self u {v}, v, mem_insert_of_mem (mem_singleton_self v), hne, hadj⟩

lemma windmillMatching_disjoint {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (hw : IsUniversalVertex G w) :
    ∀ e₁ ∈ windmillMatching G w, ∀ e₂ ∈ windmillMatching G w, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  intro e₁ he₁ e₂ he₂ hne
  rw [mem_windmillMatching_iff] at he₁ he₂
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have hxw : x ≠ w := he₁.2.1 x hx1
  have h1 := induced_non_politician_degree_one G h_friend w hw x hxw
  obtain ⟨u₁, hu1_mem, v₁, hv1_mem, hne1, hadj1⟩ := he₁.2.2
  obtain ⟨u₂, hu2_mem, v₂, hv2_mem, hne2, hadj2⟩ := he₂.2.2
  have hx_adj1 : ∃ y ∈ e₁, y ≠ x ∧ G.Adj x y := by
    have : x = u₁ ∨ x = v₁ := by
      have := he₁.1
      rw [Finset.card_eq_two] at this
      obtain ⟨a, b, hab, heq⟩ := this
      rw [heq] at hx1 hu1_mem hv1_mem
      simp only [mem_insert, mem_singleton] at hx1 hu1_mem hv1_mem
      rcases hx1 with (rfl | rfl) <;> rcases hu1_mem with (rfl | rfl) <;> rcases hv1_mem with (rfl | rfl)
      <;> tauto
    rcases this with (rfl | rfl)
    · exact ⟨v₁, hv1_mem, hne1.symm, hadj1⟩
    · exact ⟨u₁, hu1_mem, hne1, hadj1.symm⟩
  have hx_adj2 : ∃ z ∈ e₂, z ≠ x ∧ G.Adj x z := by
    have : x = u₂ ∨ x = v₂ := by
      have := he₂.1
      rw [Finset.card_eq_two] at this
      obtain ⟨a, b, hab, heq⟩ := this
      rw [heq] at hx2 hu2_mem hv2_mem
      simp only [mem_insert, mem_singleton] at hx2 hu2_mem hv2_mem
      rcases hx2 with (rfl | rfl) <;> rcases hu2_mem with (rfl | rfl) <;> rcases hv2_mem with (rfl | rfl)
      <;> tauto
    rcases this with (rfl | rfl)
    · exact ⟨v₂, hv2_mem, hne2.symm, hadj2⟩
    · exact ⟨u₂, hu2_mem, hne2, hadj2.symm⟩
  obtain ⟨y, hy_mem, hy_ne, hy_adj⟩ := hx_adj1
  obtain ⟨z, hz_mem, hz_ne, hz_adj⟩ := hx_adj2
  have hy_mem_deg : y ∈ (G.neighborFinset x).erase w := by
    rw [mem_erase, mem_neighborFinset]
    exact ⟨he₁.2.1 y hy_mem, hy_adj⟩
  have hz_mem_deg : z ∈ (G.neighborFinset x).erase w := by
    rw [mem_erase, mem_neighborFinset]
    exact ⟨he₂.2.1 z hz_mem, hz_adj⟩
  obtain ⟨single, h_single⟩ := Finset.card_eq_one.mp h1
  have hy_eq : y = single := by
    have := hy_mem_deg
    rw [h_single, mem_singleton] at this
    exact this
  have hz_eq : z = single := by
    have := hz_mem_deg
    rw [h_single, mem_singleton] at this
    exact this
  have hyz : y = z := by rw [hy_eq, hz_eq]
  have he1_eq : e₁ = {x, y} := by
    have hcard := he₁.1
    rw [Finset.card_eq_two] at hcard
    obtain ⟨a, b, hab, heq⟩ := hcard
    ext t
    simp only [heq, mem_insert, mem_singleton] at hx1 hy_mem ⊢
    rcases hx1 with (rfl | rfl) <;> rcases hy_mem with (rfl | rfl)
    · exfalso; exact hy_ne rfl
    · tauto
    · tauto
    · exfalso; exact hy_ne rfl
  have he2_eq : e₂ = {x, z} := by
    have hcard := he₂.1
    rw [Finset.card_eq_two] at hcard
    obtain ⟨a, b, hab, heq⟩ := hcard
    ext t
    simp only [heq, mem_insert, mem_singleton] at hx2 hz_mem ⊢
    rcases hx2 with (rfl | rfl) <;> rcases hz_mem with (rfl | rfl)
    · exfalso; exact hz_ne rfl
    · tauto
    · tauto
    · exfalso; exact hz_ne rfl
  have : e₁ = e₂ := by rw [he1_eq, he2_eq, hyz]
  exact hne this

lemma biUnion_windmillMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (hw : IsUniversalVertex G w) :
    ((windmillMatching G w).biUnion id) = Finset.univ.erase w := by
  ext x
  simp only [mem_biUnion, id, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨e, he, hxe⟩
    rw [mem_windmillMatching_iff] at he
    exact he.2.1 x hxe
  · intro hxw
    have h1 := induced_non_politician_degree_one G h_friend w hw x hxw
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
    have hy_mem : y ∈ (G.neighborFinset x).erase w := by
      rw [hy, mem_singleton]
    rw [mem_erase, mem_neighborFinset] at hy_mem
    have h_pair := pair_mem_windmillMatching hy_mem.1 hxw hy_mem.2.symm
    refine ⟨{y, x}, h_pair, ?_⟩
    simp

/-- **Friendship Graph Odd Vertex Count:**
    The number of vertices in any friendship graph is odd ($|V| = 2k + 1$). -/
theorem friendship_graph_odd_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) :
    Odd (Fintype.card V) := by
  obtain ⟨w, hw⟩ := exists_universal_of_friendship G h_friend
  let M := windmillMatching G w
  have h_disj : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂ :=
    windmillMatching_disjoint h_friend w hw
  have h_card_sum : (M.biUnion id).card = ∑ e ∈ M, e.card :=
    Finset.card_biUnion (fun e₁ he₁ e₂ he₂ hne => h_disj e₁ he₁ e₂ he₂ hne)
  have h_each_card : ∀ e ∈ M, e.card = 2 := by
    intro e he
    rw [mem_windmillMatching_iff] at he
    exact he.1
  have h_sum_two : (∑ e ∈ M, e.card) = 2 * M.card := by
    calc (∑ e ∈ M, e.card) = ∑ e ∈ M, 2 := Finset.sum_congr rfl h_each_card
    _ = M.card * 2 := Finset.sum_const 2
    _ = 2 * M.card := by ring
  have h_union := biUnion_windmillMatching G h_friend w hw
  rw [h_union, card_erase_of_mem (mem_univ w), card_univ] at h_card_sum
  have h_card_v : Fintype.card V = 2 * M.card + 1 := by
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  exact ⟨M.card, h_card_v⟩

/-- Predicate defining a windmill graph $Wd(k, 2)$: a central vertex `w` connected to
    `k` vertex-disjoint triangles. -/
def IsWindmillGraph (G : SimpleGraph V) (w : V) (k : ℕ) : Prop :=
  IsUniversalVertex G w ∧
  Fintype.card V = 2 * k + 1 ∧
  ∃ (matching : Finset (Finset V)),
    matching.card = k ∧
    (∀ e ∈ matching, e.card = 2 ∧ w ∉ e) ∧
    (∀ e₁ ∈ matching, ∀ e₂ ∈ matching, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
    (∀ u v, u ≠ w → v ≠ w → (G.Adj u v ↔ {u, v} ∈ matching))

/-- **Windmill Classification Theorem (Erdős–Rényi–Sós 1966):**
    Every graph satisfying the friendship property is a windmill graph $Wd(k, 2)$. -/
theorem friendship_is_windmill (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) :
    ∃ (w : V) (k : ℕ), IsWindmillGraph G w k := by
  obtain ⟨w, hw⟩ := exists_universal_of_friendship G h_friend
  let M := windmillMatching G w
  have h_odd := friendship_graph_odd_card G h_friend
  refine ⟨w, M.card, hw, ?_, M, rfl, ?_, ?_, ?_⟩
  · have h_disj : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂ :=
      windmillMatching_disjoint h_friend w hw
    have h_card_sum : (M.biUnion id).card = ∑ e ∈ M, e.card :=
      Finset.card_biUnion (fun e₁ he₁ e₂ he₂ hne => h_disj e₁ he₁ e₂ he₂ hne)
    have h_each_card : ∀ e ∈ M, e.card = 2 := fun e he => (mem_windmillMatching_iff.mp he).1
    have h_sum_two : (∑ e ∈ M, e.card) = 2 * M.card := by
      calc (∑ e ∈ M, e.card) = ∑ e ∈ M, 2 := Finset.sum_congr rfl h_each_card
      _ = M.card * 2 := Finset.sum_const 2
      _ = 2 * M.card := by ring
    have h_union := biUnion_windmillMatching G h_friend w hw
    rw [h_union, card_erase_of_mem (mem_univ w), card_univ] at h_card_sum
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  · intro e he
    rw [mem_windmillMatching_iff] at he
    refine ⟨he.1, ?_⟩
    intro hw_mem
    exact (he.2.1 w hw_mem) rfl
  · exact windmillMatching_disjoint h_friend w hw
  · intro u v huw hvw
    constructor
    · intro hadj
      exact pair_mem_windmillMatching huw hvw hadj
    · intro he_mem
      rw [mem_windmillMatching_iff] at he_mem
      obtain ⟨u₀, hu0, v₀, hv0, hne0, hadj0⟩ := he_mem.2.2
      simp only [mem_insert, mem_singleton] at hu0 hv0
      rcases hu0 with (rfl | rfl) <;> rcases hv0 with (rfl | rfl)
      · exfalso; exact hne0 rfl
      · exact hadj0
      · exact hadj0.symm
      · exfalso; exact hne0 rfl

/-- The total edge count of any friendship graph on $2k + 1$ vertices is exactly $3k$. -/
theorem friendship_edge_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (k : ℕ)
    (h_wind : IsWindmillGraph G w k) :
    G.edgeFinset.card = 3 * k := by
  have h_deg_sum := G.sum_degrees_eq_twice_card_edges
  obtain ⟨hw_univ, h_card_V, matching, h_m_card, h_m_two, h_m_disj, h_m_adj⟩ := h_wind
  have h_deg_w : G.degree w = 2 * k := by
    have := politician_degree G h_friend w hw_univ
    omega
  have h_deg_other (v : V) (hv : v ≠ w) : G.degree v = 2 := by
    have h1 := induced_non_politician_degree_one G h_friend w hw_univ v hv
    have h_nbr : G.neighborFinset v = insert w ((G.neighborFinset v).erase w) := by
      ext x
      simp only [mem_neighborFinset, mem_insert, mem_erase]
      constructor
      · intro hadj
        by_cases hxw : x = w
        · left; exact hxw
        · right; exact ⟨hxw, hadj⟩
      · rintro (rfl | ⟨hxw, hadj⟩)
        · exact (hw_univ v hv).symm
        · exact hadj
    have hw_not_mem : w ∉ (G.neighborFinset v).erase w := by simp [mem_erase]
    rw [degree, h_nbr, card_insert_of_notMem hw_not_mem, h1]
  have h_sum : (∑ v : V, G.degree v) = G.degree w + ∑ v ∈ Finset.univ.erase w, G.degree v := by
    have : (Finset.univ : Finset V) = insert w (Finset.univ.erase w) := (insert_erase (mem_univ w)).symm
    nth_rw 1 [this]
    rw [Finset.sum_insert (by simp [mem_erase])]
  have h_sum_other : (∑ v ∈ Finset.univ.erase w, G.degree v) = 2 * (2 * k) := by
    have h_each : ∀ v ∈ Finset.univ.erase w, G.degree v = 2 := by
      intro v hv
      exact h_deg_other v (mem_erase.mp hv).1
    calc (∑ v ∈ Finset.univ.erase w, G.degree v) = ∑ v ∈ Finset.univ.erase w, 2 := Finset.sum_congr rfl h_each
    _ = (Finset.univ.erase w).card * 2 := Finset.sum_const 2
    _ = (Fintype.card V - 1) * 2 := by rw [card_erase_of_mem (mem_univ w), card_univ]
    _ = (2 * k) * 2 := by rw [h_card_V]; omega
    _ = 2 * (2 * k) := by ring
  rw [h_deg_w, h_sum_other] at h_sum
  omega

end FriendshipWindmill
