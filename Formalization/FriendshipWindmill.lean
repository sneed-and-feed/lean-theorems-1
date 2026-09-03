import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Formalization.FriendshipTheorem

open Finset SimpleGraph

namespace FriendshipWindmill

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (politician) in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

omit [Nonempty V] in
theorem politician_degree (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)
    (h_univ : IsUniversalVertex G w) : G.degree w = Fintype.card V - 1 := by
  rw [degree, show G.neighborFinset w = Finset.univ.erase w by ext u; simp [mem_neighborFinset]; exact ⟨fun h => h.ne.symm, h_univ u⟩]
  rw [card_erase_of_mem (mem_univ w), card_univ]

omit [Nonempty V] in
theorem induced_non_politician_degree_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V)
    (h_univ : IsUniversalVertex G w) (v : V) (hv : v ≠ w) :
    ((G.neighborFinset v).erase w).card = 1 := by
  rw [← h_friend v w hv]
  congr 1; ext u; simp only [mem_inter, mem_erase, mem_neighborFinset]
  have h := h_univ u
  aesop

omit [Nonempty V] in
lemma card_ne_two_of_friendship (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) : Fintype.card V ≠ 2 := by
  intro h_two
  have h_univ_card : (Finset.univ : Finset V).card = 2 := by rw [card_univ, h_two]
  obtain ⟨a, b, hab, h_univ_eq⟩ := Finset.card_eq_two.mp h_univ_card
  have hall (x : V) : x = a ∨ x = b := by simpa [h_univ_eq] using mem_univ x
  have h_empty : (G.neighborFinset a ∩ G.neighborFinset b) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro x; simp only [mem_inter, mem_neighborFinset]
    rcases hall x with (rfl | rfl) <;> rintro ⟨h1, h2⟩
    · exact h1.ne rfl
    · exact h2.ne rfl
  have h_inter := h_friend a b hab
  rw [h_empty, Finset.card_empty] at h_inter
  omega

lemma exists_universal_of_friendship (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) : ∃ w : V, IsUniversalVertex G w := by
  rcases le_or_gt 3 (Fintype.card V) with h3 | h_lt
  · exact FriendshipTheorem.friendship_theorem G h_friend h3
  · have h_pos : 0 < Fintype.card V := Fintype.card_pos
    have h2 := card_ne_two_of_friendship G h_friend
    have h_card : Fintype.card V = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (by rw [card_univ, h_card] : (univ : Finset V).card = 1)
    exact ⟨w, fun v hv => False.elim <| hv <| by simpa [hw] using mem_univ v⟩

def windmillMatching (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) : Finset (Finset V) :=
  ((Finset.univ.erase w).powersetCard 2).filter (fun e => ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v)

omit [Nonempty V] in
lemma mem_windmillMatching_iff {G : SimpleGraph V} [DecidableRel G.Adj] {w : V} {e : Finset V} :
    e ∈ windmillMatching G w ↔ e.card = 2 ∧ (∀ x ∈ e, x ≠ w) ∧ (∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ G.Adj u v) := by
  simp [windmillMatching, subset_erase]; aesop

omit [Nonempty V] in
lemma pair_mem_windmillMatching {G : SimpleGraph V} [DecidableRel G.Adj] {w u v : V}
    (hu : u ≠ w) (hv : v ≠ w) (hadj : G.Adj u v) : ({u, v} : Finset V) ∈ windmillMatching G w := by
  rw [mem_windmillMatching_iff]; have hne := hadj.ne
  refine ⟨Finset.card_pair hne, by aesop, u, by simp, v, by simp, hne, hadj⟩

omit [Nonempty V] in
lemma get_nbr_in_windmill {G : SimpleGraph V} [DecidableRel G.Adj] {w x y: V} {e : Finset V}
    (he : e ∈ windmillMatching G w) (hx : x ∈ e) (hy : y ∈ e.erase x) :
    y ∈ (G.neighborFinset x).erase w := by
  rw [mem_windmillMatching_iff] at he
  rw [mem_erase, mem_neighborFinset]
  refine ⟨he.2.1 y (mem_erase.mp hy).2, ?_⟩
  rcases he.2.2 with ⟨u, hu, v, hv, huv, hadj⟩
  have eq_uv : {u, v} = e := by
    apply eq_of_subset_of_card_le
    · intro z hz; rw [mem_insert, mem_singleton] at hz; rcases hz with rfl|rfl <;> assumption
    · rw [he.1, Finset.card_pair huv]
  have e_eq : e = {u, v} := eq_uv.symm
  have hx2 := hx; have hy2 := (mem_erase.mp hy).2; have hyne := (mem_erase.mp hy).1
  rw [e_eq] at hx2 hy2
  simp only [mem_insert, mem_singleton] at hx2 hy2
  rcases hx2 with rfl | rfl
  · rcases hy2 with rfl | rfl
    · exact (hyne rfl).elim
    · exact hadj
  · rcases hy2 with rfl | rfl
    · exact hadj.symm
    · exact (hyne rfl).elim

omit [Nonempty V] in
lemma windmillMatching_disjoint {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (hw : IsUniversalVertex G w) :
    ∀ e₁ ∈ windmillMatching G w, ∀ e₂ ∈ windmillMatching G w, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
  intro e₁ he₁ e₂ he₂ hne
  rw [Finset.disjoint_left]; intro x hx1 hx2
  have hxw : x ≠ w := (mem_windmillMatching_iff.mp he₁).2.1 x hx1
  have h1 := induced_non_politician_degree_one G h_friend w hw x hxw
  obtain ⟨y1, hy1⟩ := Finset.card_eq_one.mp h1
  have h_eq (e : Finset V) (he : e ∈ windmillMatching G w) (hx : x ∈ e) : e.erase x = {y1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · have h_c : (e.erase x).card = 1 := by rw [card_erase_of_mem hx, (mem_windmillMatching_iff.mp he).1]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h_c
      have hz_mem : z ∈ e.erase x := by rw [hz]; exact mem_singleton_self z
      have : z ∈ (G.neighborFinset x).erase w := get_nbr_in_windmill he hx hz_mem
      have y1_eq_z : y1 = z := by
        have hyz := this
        rw [hy1, mem_singleton] at hyz
        exact hyz.symm
      rw [y1_eq_z]; exact hz_mem
    · intro z hz
      have : z ∈ (G.neighborFinset x).erase w := get_nbr_in_windmill he hx hz
      rw [hy1, mem_singleton] at this; exact this
  have heq : e₁ = e₂ := by
    calc e₁ = insert x (e₁.erase x) := (insert_erase hx1).symm
      _ = insert x {y1} := by rw [h_eq e₁ he₁ hx1]
      _ = insert x (e₂.erase x) := by rw [h_eq e₂ he₂ hx2]
      _ = e₂ := insert_erase hx2
  exact hne heq

omit [Nonempty V] in
lemma biUnion_windmillMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (hw : IsUniversalVertex G w) :
    ((windmillMatching G w).biUnion id) = Finset.univ.erase w := by
  ext x; simp only [mem_biUnion, id, mem_erase, mem_univ, and_true]
  refine ⟨fun ⟨e, he, hxe⟩ => (mem_windmillMatching_iff.mp he).2.1 x hxe, fun hxw => ?_⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (induced_non_politician_degree_one G h_friend w hw x hxw)
  have hy_mem : y ∈ (G.neighborFinset x).erase w := by rw [hy]; exact mem_singleton_self y
  rw [mem_erase, mem_neighborFinset] at hy_mem
  exact ⟨{y, x}, pair_mem_windmillMatching hy_mem.1 hxw hy_mem.2.symm, by simp⟩

/-- **Friendship Graph Odd Vertex Count:**
    The number of vertices in any friendship graph is odd ($|V| = 2k + 1$). -/
theorem friendship_graph_odd_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) : Odd (Fintype.card V) := by
  obtain ⟨w, hw⟩ := exists_universal_of_friendship G h_friend
  let M := windmillMatching G w
  have h_sum : (M.biUnion id).card = ∑ e ∈ M, e.card :=
    Finset.card_biUnion (windmillMatching_disjoint h_friend w hw)
  have h_card : Fintype.card V - 1 = 2 * M.card := by
    calc Fintype.card V - 1 = (Finset.univ.erase w).card := by rw [card_erase_of_mem (mem_univ w), card_univ]
      _ = (M.biUnion id).card := by rw [biUnion_windmillMatching G h_friend w hw]
      _ = ∑ e ∈ M, e.card := h_sum
      _ = ∑ e ∈ M, 2 := Finset.sum_congr rfl (fun e he => (mem_windmillMatching_iff.mp he).1)
      _ = M.card * 2 := Finset.sum_const 2
      _ = 2 * M.card := by ring
  have : 0 < Fintype.card V := Fintype.card_pos
  exact ⟨M.card, by omega⟩

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
    (h_friend : HasFriendshipProperty G) : ∃ (w : V) (k : ℕ), IsWindmillGraph G w k := by
  obtain ⟨w, hw⟩ := exists_universal_of_friendship G h_friend
  let M := windmillMatching G w
  refine ⟨w, M.card, hw, ?_, M, rfl, ?_, windmillMatching_disjoint h_friend w hw, ?_⟩
  · have h_sum : (M.biUnion id).card = ∑ e ∈ M, e.card :=
      Finset.card_biUnion (windmillMatching_disjoint h_friend w hw)
    have h_card : Fintype.card V - 1 = 2 * M.card := by
      calc Fintype.card V - 1 = (Finset.univ.erase w).card := by rw [card_erase_of_mem (mem_univ w), card_univ]
        _ = (M.biUnion id).card := by rw [biUnion_windmillMatching G h_friend w hw]
        _ = ∑ e ∈ M, e.card := h_sum
        _ = ∑ e ∈ M, 2 := Finset.sum_congr rfl (fun e he => (mem_windmillMatching_iff.mp he).1)
        _ = M.card * 2 := Finset.sum_const 2
        _ = 2 * M.card := by ring
    have : 0 < Fintype.card V := Fintype.card_pos
    omega
  · intro e he
    have he2 := mem_windmillMatching_iff.mp he
    exact ⟨he2.1, fun hw_mem => he2.2.1 w hw_mem rfl⟩
  · intro u v huw hvw
    constructor
    · exact pair_mem_windmillMatching huw hvw
    · intro he_mem
      have he2 := mem_windmillMatching_iff.mp he_mem
      obtain ⟨u₀, hu0, v₀, hv0, hne0, hadj0⟩ := he2.2.2
      simp only [mem_insert, mem_singleton] at hu0 hv0
      rcases hu0 with (rfl|rfl) <;> rcases hv0 with (rfl|rfl)
      · exact (hne0 rfl).elim
      · exact hadj0
      · exact hadj0.symm
      · exact (hne0 rfl).elim

omit [Nonempty V] in
/-- The total edge count of any friendship graph on $2k + 1$ vertices is exactly $3k$. -/
theorem friendship_edge_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (k : ℕ)
    (h_wind : IsWindmillGraph G w k) : G.edgeFinset.card = 3 * k := by
  have h_deg_sum := G.sum_degrees_eq_twice_card_edges
  obtain ⟨hw_univ, h_card_V, matching, h_m_card, h_m_two, h_m_disj, h_m_adj⟩ := h_wind
  have h_deg_w : G.degree w = 2 * k := by
    have := politician_degree G w hw_univ
    omega
  have h_deg_other (v : V) (hv : v ≠ w) : G.degree v = 2 := by
    have h1 := induced_non_politician_degree_one G h_friend w hw_univ v hv
    have h_nbr : G.neighborFinset v = insert w ((G.neighborFinset v).erase w) := by
      ext x; simp only [mem_neighborFinset, mem_insert, mem_erase]
      have h := hw_univ v hv
      constructor
      · intro hadj; by_cases hxw : x = w
        · exact Or.inl hxw
        · exact Or.inr ⟨hxw, hadj⟩
      · rintro (rfl | ⟨_, hadj⟩)
        · exact h.symm
        · exact hadj
    rw [degree, h_nbr, card_insert_of_notMem (by simp [mem_erase]), h1]
  have h_sum : (∑ v : V, G.degree v) = G.degree w + ∑ v ∈ Finset.univ.erase w, G.degree v := by
    nth_rw 1 [show (Finset.univ : Finset V) = insert w (Finset.univ.erase w) from (insert_erase (mem_univ w)).symm]
    rw [Finset.sum_insert (by simp [mem_erase])]
  have h_sum_other : (∑ v ∈ Finset.univ.erase w, G.degree v) = 2 * (2 * k) := by
    calc (∑ v ∈ Finset.univ.erase w, G.degree v) = ∑ v ∈ Finset.univ.erase w, 2 := Finset.sum_congr rfl (fun v hv => h_deg_other v (mem_erase.mp hv).1)
    _ = (Finset.univ.erase w).card * 2 := Finset.sum_const 2
    _ = (Fintype.card V - 1) * 2 := by rw [card_erase_of_mem (mem_univ w), card_univ]
    _ = (2 * k) * 2 := by rw [h_card_V]; omega
    _ = 2 * (2 * k) := by ring
  rw [h_deg_w, h_sum_other] at h_sum
  omega

/-- **The Friendship Windmill Structure Theorem (Erdős–Rényi–Sós 1966)**:
Every finite graph satisfying the friendship property is a windmill graph $Wd(k, 2)$ consisting of $k$ triangles sharing a universal vertex. -/
theorem friendship_windmill (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) : ∃ (w : V) (k : ℕ), IsWindmillGraph G w k :=
  friendship_is_windmill G h_friend

end FriendshipWindmill

export FriendshipWindmill (HasFriendshipProperty IsUniversalVertex IsWindmillGraph friendship_windmill)
