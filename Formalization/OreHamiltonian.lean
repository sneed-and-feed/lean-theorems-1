import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max

open SimpleGraph
open scoped List

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph.Walk

lemma IsPath.length_le_card {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  have hlen : p.support.length = p.length + 1 := p.length_support
  have hcard : p.support.toFinset.card ≤ Fintype.card V := Finset.card_le_univ _
  have hnodup : p.support.toFinset.card = p.support.length := List.toFinset_card_of_nodup hp.support_nodup
  omega

end SimpleGraph.Walk

lemma exists_maximal_path (G : SimpleGraph V) [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧
      ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length := by
  classical
  let s : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter
    (fun n => ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n)
  have hs0 : 0 ∈ s := by
    obtain ⟨x⟩ := ‹Nonempty V›
    simp only [s, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ⟨x, x, Walk.nil, Walk.IsPath.nil, rfl⟩⟩
  have hs_nonempty : s.Nonempty := ⟨0, hs0⟩
  let k := s.max' hs_nonempty
  have hk_mem : k ∈ s := Finset.max'_mem s hs_nonempty
  simp only [s, Finset.mem_filter, Finset.mem_range] at hk_mem
  rcases hk_mem.2 with ⟨u, v, p, hp, hplen⟩
  refine ⟨u, v, p, hp, fun {u' v'} q hq => ?_⟩
  have hq_lt : q.length < Fintype.card V + 1 := by
    have := hq.length_le_card
    omega
  have hq_mem : q.length ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_range]
    exact ⟨hq_lt, ⟨u', v', q, hq, rfl⟩⟩
  have := Finset.le_max' s q.length hq_mem
  omega

set_option linter.unusedSectionVars false


lemma neighbor_start_mem_support_of_maximal {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    {w : V} (hw : G.Adj u w) : w ∈ p.support := by
  by_contra hnot
  have hlen := hmax (p.cons hw.symm) (by simp [Walk.isPath_def, hnot, hp.support_nodup])
  revert hlen; simp [Walk.length_cons]

lemma neighbor_end_mem_support_of_maximal {G : SimpleGraph V} {u v : V} {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
    {w : V} (hw : G.Adj v w) : w ∈ p.support := by
  by_contra hnot
  have hq_path : (p.concat hw).IsPath := by
    rw [Walk.isPath_def, Walk.support_concat, List.nodup_append]
    refine ⟨hp.support_nodup, List.nodup_singleton w, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb; rintro rfl; exact hnot ha
  have hlen := hmax (p.concat hw) hq_path
  revert hlen; simp [Walk.length_concat]

lemma card_I_u_of_maximal {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    (((Finset.range p.length).filter (fun i => G.Adj u (p.getVert (i + 1)))).card) = G.degree u := by
  classical
  let I := (Finset.range p.length).filter (fun i => G.Adj u (p.getVert (i + 1)))
  have hinj : Set.InjOn (fun i => p.getVert (i + 1)) I := by
    intro i hi j hj hij
    have hi_lt : i < p.length := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj_lt : j < p.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hi_le : i + 1 ≤ p.length := by omega
    have hj_le : j + 1 ≤ p.length := by omega
    have h_eq := hp.getVert_injOn (by simp [hi_le]) (by simp [hj_le]) hij
    omega
  have h_img : I.image (fun i => p.getVert (i + 1)) = G.neighborFinset u := by
    ext w
    simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_range, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨i, ⟨hi, hadj⟩, rfl⟩
      exact hadj
    · intro hw
      have hw_supp := neighbor_start_mem_support_of_maximal hp hmax hw
      obtain ⟨m, hvm, hm_le⟩ := Walk.mem_support_iff_exists_getVert.mp hw_supp
      have hm_pos : m ≠ 0 := by
        rintro rfl
        rw [Walk.getVert_zero] at hvm
        exact hw.ne hvm
      refine ⟨m - 1, ⟨by omega, ?_⟩, ?_⟩
      · have : m - 1 + 1 = m := by omega
        rw [this, hvm]
        exact hw
      · have : m - 1 + 1 = m := by omega
        rw [this, hvm]
  rw [SimpleGraph.degree, ← h_img, Finset.card_image_of_injOn hinj]

lemma card_I_v_of_maximal {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    (((Finset.range p.length).filter (fun i => G.Adj v (p.getVert i))).card) = G.degree v := by
  classical
  let I := (Finset.range p.length).filter (fun i => G.Adj v (p.getVert i))
  have hinj : Set.InjOn (fun i => p.getVert i) I := by
    intro i hi j hj hij
    have hi_lt : i < p.length := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj_lt : j < p.length := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hi_le : i ≤ p.length := by omega
    have hj_le : j ≤ p.length := by omega
    have := hp.getVert_injOn (by simp [hi_le]) (by simp [hj_le]) hij
    exact this
  have h_img : I.image (fun i => p.getVert i) = G.neighborFinset v := by
    ext w
    simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_range, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨i, ⟨hi, hadj⟩, rfl⟩
      exact hadj
    · intro hw
      have hw_supp := neighbor_end_mem_support_of_maximal hp hmax hw
      obtain ⟨m, hvm, hm_le⟩ := Walk.mem_support_iff_exists_getVert.mp hw_supp
      have hm_lt : m < p.length := by
        by_contra! hge
        have : m = p.length := by omega
        subst this
        rw [Walk.getVert_length] at hvm
        exact hw.ne hvm
      refine ⟨m, ⟨by omega, ?_⟩, ?_⟩
      · rw [hvm]
        exact hw
      · exact hvm
  rw [SimpleGraph.degree, ← h_img, Finset.card_image_of_injOn hinj]

lemma exists_cross_adj_of_maximal {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}
    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ x y : V, x ≠ y → ¬ G.Adj x y → Fintype.card V ≤ G.degree x + G.degree y)
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    ∃ i < p.length, G.Adj u (p.getVert (i + 1)) ∧ G.Adj v (p.getVert i) := by
  classical
  have hk_pos : 0 < p.length := by
    by_contra! hzero
    have hk0 : p.length = 0 := by omega
    have hno_adj : ∀ x y : V, ¬ G.Adj x y := by
      intro x y hadj
      have hq : hadj.toWalk.IsPath := by
        rw [Walk.isPath_def]
        simp [hadj.ne]
      have hlen := hmax hadj.toWalk hq
      simp only [Adj.length_toWalk] at hlen
      omega
    have hdeg_zero : ∀ x : V, G.degree x = 0 := by
      intro x
      rw [SimpleGraph.degree, Finset.card_eq_zero]
      ext w
      simp [mem_neighborFinset, hno_adj x w]


    have : 1 < Fintype.card V := by omega
    have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp this
    obtain ⟨x, y, hxy⟩ := exists_pair_ne V
    have hore_xy := hore x y hxy (hno_adj x y)
    rw [hdeg_zero x, hdeg_zero y] at hore_xy
    omega
  let I_u := (Finset.range p.length).filter (fun i => G.Adj u (p.getVert (i + 1)))
  let I_v := (Finset.range p.length).filter (fun i => G.Adj v (p.getVert i))
  have hI_u : I_u.card = G.degree u := card_I_u_of_maximal hp hmax
  have hI_v : I_v.card = G.degree v := card_I_v_of_maximal hp hmax
  by_cases hadj_uv : G.Adj u v
  · refine ⟨p.length - 1, by omega, ?_, ?_⟩
    · have : p.length - 1 + 1 = p.length := by omega
      rw [this, Walk.getVert_length]
      exact hadj_uv
    · have hstep := Walk.adj_getVert_succ p (by omega : p.length - 1 < p.length)
      have : p.length - 1 + 1 = p.length := by omega
      rw [this, Walk.getVert_length] at hstep
      exact hstep.symm
  · have huv_ne : u ≠ v := by
      rintro rfl
      have h0 : (0 : ℕ) ∈ {i | i ≤ p.length} := by simp
      have hl : p.length ∈ {i | i ≤ p.length} := by simp
      have h_eq : p.getVert 0 = p.getVert p.length := by
        rw [Walk.getVert_zero, Walk.getVert_length]
      have := hp.getVert_injOn h0 hl h_eq
      omega
    have hore_val := hore u v huv_ne hadj_uv
    have h_union_le : (I_u ∪ I_v).card ≤ p.length := by
      have : I_u ∪ I_v ⊆ Finset.range p.length := by
        intro x hx
        simp only [Finset.mem_union, I_u, I_v, Finset.mem_filter] at hx
        rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩ <;> exact hx
      have hcard := Finset.card_le_card this
      simp only [Finset.card_range] at hcard
      exact hcard
    have h_inter_pos : (I_u ∩ I_v).card > 0 := by
      have h_ie := Finset.card_union_add_card_inter I_u I_v
      have hlen_lt := hp.length_le_card
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h_inter_pos
    simp only [Finset.mem_inter, I_u, I_v, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨i, hi.1.1, hi.1.2, hi.2.2⟩

lemma two_le_length_of_maximal {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} {p : G.Walk u v}

    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ x y : V, x ≠ y → ¬ G.Adj x y → Fintype.card V ≤ G.degree x + G.degree y)
    (hp : p.IsPath)
    (hmax : ∀ {u' v' : V} (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length) :
    2 ≤ p.length := by
  classical
  obtain ⟨i, hi, hadj_u, hadj_v⟩ := exists_cross_adj_of_maximal hn hore hp hmax
  by_contra! hlt
  have hlen1 : p.length = 1 := by
    have : 0 < p.length := by omega
    omega
  have hdeg_le_one : ∀ x : V, G.degree x ≤ 1 := by
    intro x
    by_contra! hdeg2
    have : 2 ≤ (G.neighborFinset x).card := hdeg2
    obtain ⟨y, hy, z, hz, hyz⟩ : ∃ y ∈ G.neighborFinset x, ∃ z ∈ G.neighborFinset x, y ≠ z := by
      have : 1 < (G.neighborFinset x).card := by omega
      have : (G.neighborFinset x).Nontrivial := Finset.one_lt_card_iff_nontrivial.mp this
      obtain ⟨y, hy, z, hz, hyz⟩ := this
      exact ⟨y, hy, z, hz, hyz⟩
    rw [SimpleGraph.mem_neighborFinset] at hy hz
    have hq_path : ((Walk.nil.cons hz).cons hy.symm).IsPath := by
      rw [Walk.isPath_def]
      simp only [Walk.support_cons, Walk.support_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, not_or, and_true, not_false_eq_true]
      refine ⟨⟨hy.ne', hyz⟩, hz.ne, trivial, List.nodup_nil⟩


    have hlen := hmax ((Walk.nil.cons hz).cons hy.symm) hq_path
    simp only [Walk.length_cons, Walk.length_nil] at hlen
    omega
  have h_not_complete : ∃ x y : V, x ≠ y ∧ ¬ G.Adj x y := by
    by_contra! hall_adj
    obtain ⟨x⟩ : Nonempty V := by
      have : 0 < Fintype.card V := by omega
      exact Fintype.card_pos_iff.mp this
    have hdeg_x : G.degree x = Fintype.card V - 1 := by
      rw [SimpleGraph.degree]
      have : G.neighborFinset x = Finset.univ.erase x := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hw
          exact hw.ne'
        · intro hw_ne
          exact hall_adj x w hw_ne.symm
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    have hdeg_x_le := hdeg_le_one x
    omega

  obtain ⟨x, y, hxy, hnot_adj⟩ := h_not_complete
  have hore_xy := hore x y hxy hnot_adj
  have hx_le := hdeg_le_one x
  have hy_le := hdeg_le_one y
  omega

def oreCycle {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (i : ℕ)

    (hadj_u : G.Adj u (p.getVert (i + 1)))
    (hadj_v : G.Adj v (p.getVert i)) : G.Walk u u :=
  let p1 := (p.take i).concat hadj_v.symm
  let p2 := (p.drop (i + 1)).reverse
  (p1.append p2).concat hadj_u.symm

lemma oreCycle_length {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (i : ℕ) (hi : i < p.length)
    (hadj_u : G.Adj u (p.getVert (i + 1)))
    (hadj_v : G.Adj v (p.getVert i)) :
    (oreCycle p i hadj_u hadj_v).length = p.length + 1 := by
  simp only [oreCycle, Walk.length_concat, Walk.length_append, Walk.take_length,
    Walk.length_reverse, Walk.drop_length]
  omega

lemma oreCycle_support_tail_perm {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (i : ℕ)
    (hi : i < p.length)
    (hadj_u : G.Adj u (p.getVert (i + 1)))
    (hadj_v : G.Adj v (p.getVert i)) :
    (oreCycle p i hadj_u hadj_v).support.tail ~ p.support := by
  classical
  let C := oreCycle p i hadj_u hadj_v
  have hmin : min (i + 1) p.length = i + 1 := by omega
  have h_supp_C : C.support = (p.support.take (i + 1)) ++ [v] ++
      ((p.support.drop (i + 1)).reverse.tail) ++ [u] := by
    simp only [C, oreCycle, Walk.support_concat, Walk.support_append, Walk.support_take,
      Walk.support_reverse, Walk.drop_support_eq_support_drop_min, hmin]
  cases p with
  | nil =>
    simp only [Walk.length_nil] at hi
    omega
  | cons hadj_w q =>

    have h_p_supp : (Walk.cons hadj_w q).support = u :: q.support := by simp
    have h_q_end : q.support = q.support.dropLast ++ [v] := by
      have h := List.dropLast_append_getLast q.support_ne_nil
      rw [q.getLast_support] at h
      exact h.symm
    have htake : (u :: q.support).take (i + 1) = u :: (q.support.take i) := rfl
    have hdrop : (u :: q.support).drop (i + 1) = q.support.drop i := rfl
    have hq_len : i ≤ q.support.dropLast.length := by
      have : q.support.length = q.length + 1 := q.length_support
      have : q.support.dropLast.length = q.length := by
        rw [h_q_end] at this
        simp only [List.length_append, List.length_singleton] at this
        omega
      simp only [Walk.length_cons] at hi
      omega
    have hdrop_q : q.support.drop i = (q.support.dropLast.drop i) ++ [v] := by
      conv_lhs => rw [h_q_end]
      exact List.drop_append_of_le_length hq_len
    have hrev : (q.support.drop i).reverse = v :: (q.support.dropLast.drop i).reverse := by
      rw [hdrop_q, List.reverse_append, List.reverse_singleton, List.singleton_append]
    have htail_C : C.support.tail = (q.support.take i) ++ [v] ++ (q.support.dropLast.drop i).reverse ++ [u] := by
      have h1 : C.support = u :: ((q.support.take i) ++ [v] ++ (q.support.dropLast.drop i).reverse ++ [u]) := by
        rw [h_supp_C, h_p_supp, htake, hdrop, hrev, List.tail_cons]
        rfl
      rw [h1, List.tail_cons]
    rw [htail_C, h_p_supp]
    let A := q.support.take i
    let B := q.support.dropLast.drop i
    have h1 : A ++ [v] ++ B.reverse ++ [u] ~ [u] ++ (A ++ [v] ++ B.reverse) := by
      have : A ++ [v] ++ B.reverse ++ [u] = (A ++ [v] ++ B.reverse) ++ [u] := by
        simp only [List.append_assoc, List.singleton_append]
      rw [this]
      exact List.perm_append_comm
    have h2 : [u] ++ (A ++ [v] ++ B.reverse) ~ [u] ++ (A ++ (B.reverse ++ [v])) := by
      have : A ++ [v] ++ B.reverse = A ++ ([v] ++ B.reverse) := by simp only [List.append_assoc]
      rw [this]
      refine List.Perm.append_left [u] (List.Perm.append_left A ?_)
      exact List.perm_append_comm
    have h3 : [u] ++ (A ++ (B.reverse ++ [v])) ~ [u] ++ (A ++ (B ++ [v])) := by
      refine List.Perm.append_left [u] (List.Perm.append_left A ?_)
      exact List.Perm.append_right [v] (List.reverse_perm B)
    have h4 : [u] ++ (A ++ (B ++ [v])) = u :: q.support := by
      have : A ++ (B ++ [v]) = q.support := by
        dsimp [A, B]
        rw [← hdrop_q]
        exact List.take_append_drop i q.support
      rw [this]
      rfl
    exact ((h1.trans h2).trans h3).trans (by rw [h4])

lemma oreCycle_isCycle {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (i : ℕ)

    (hi : i < p.length)
    (hadj_u : G.Adj u (p.getVert (i + 1)))
    (hadj_v : G.Adj v (p.getVert i))
    (hp : p.IsPath)
    (hlen2 : 2 ≤ p.length) :
    (oreCycle p i hadj_u hadj_v).IsCycle := by
  let C := oreCycle p i hadj_u hadj_v
  have hlen_eq : C.length = p.length + 1 := oreCycle_length p i hi hadj_u hadj_v
  have hlen : 3 ≤ C.length := by omega

  have hperm := oreCycle_support_tail_perm i hi hadj_u hadj_v
  have hnodup : C.support.tail.Nodup := by
    rw [hperm.nodup_iff]
    exact hp.support_nodup
  have hpath_tail : C.tail.IsPath := by
    rw [Walk.isPath_def]
    have hnot_nil : ¬ C.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
    rw [Walk.support_tail_of_not_nil C hnot_nil]
    exact hnodup
  exact Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨hpath_tail, hlen⟩

lemma mem_support_oreCycle_iff {G : SimpleGraph V} {u v : V} {p : G.Walk u v} (i : ℕ)
    (hi : i < p.length)
    (hadj_u : G.Adj u (p.getVert (i + 1)))
    (hadj_v : G.Adj v (p.getVert i)) (w : V) :
    w ∈ (oreCycle p i hadj_u hadj_v).support ↔ w ∈ p.support := by
  let C := oreCycle p i hadj_u hadj_v
  have hperm := oreCycle_support_tail_perm i hi hadj_u hadj_v
  rw [Walk.mem_support_iff]
  constructor
  · rintro (rfl | hw)
    · exact p.start_mem_support
    · exact hperm.mem_iff.mp hw
  · intro hw
    by_cases hwu : w = u
    · exact .inl hwu
    · right
      exact hperm.mem_iff.mpr hw

end Helpers

/-- Ore's Theorem (1960): A simple graph on n ≥ 3 vertices with deg(u) + deg(v) ≥ n
    for all non-adjacent u ≠ v has a Hamiltonian cycle. -/
theorem ore_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := by
  classical
  have : Nonempty V := by
    have : 0 < Fintype.card V := by omega
    exact Fintype.card_pos_iff.mp this
  obtain ⟨u, v, p, hp, hmax⟩ := exists_maximal_path G
  have hlen2 : 2 ≤ p.length := two_le_length_of_maximal hn hore hp hmax
  obtain ⟨i, hi, hadj_u, hadj_v⟩ := exists_cross_adj_of_maximal hn hore hp hmax
  let C := oreCycle p i hadj_u hadj_v
  have hC_cycle : C.IsCycle := oreCycle_isCycle i hi hadj_u hadj_v hp hlen2
  have hC_len_eq : C.length = p.length + 1 := oreCycle_length p i hi hadj_u hadj_v
  have hC_supp : ∀ w : V, w ∈ C.support ↔ w ∈ p.support := mem_support_oreCycle_iff i hi hadj_u hadj_v
  let S := C.support.toFinset
  have hperm := oreCycle_support_tail_perm i hi hadj_u hadj_v
  have h_tail_nodup : C.support.tail.Nodup := hperm.nodup_iff.mpr hp.support_nodup
  have h_u_tail : u ∈ C.support.tail := hperm.mem_iff.mpr p.start_mem_support
  have h_toFinset : C.support.toFinset = C.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset, Walk.mem_support_iff]
    constructor
    · rintro (rfl | hx)
      · exact h_u_tail
      · exact hx
    · intro hx
      exact .inr hx
  have hS_card : S.card = C.length := by
    dsimp [S]
    rw [h_toFinset, List.toFinset_card_of_nodup h_tail_nodup, hperm.length_eq, p.length_support, hC_len_eq]
  have hC_len_card : C.length = Fintype.card V := by
    by_contra! hC_lt
    have hS_ne_univ : S ≠ Finset.univ := by
      intro h_univ
      have : S.card = Fintype.card V := by rw [h_univ, Finset.card_univ]
      omega
    have h_not_in_S : ∃ w : V, w ∉ S := by
      by_contra! hall_in
      have : S = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        exact hall_in x
      exact hS_ne_univ this
    obtain ⟨w, hw⟩ := h_not_in_S
    by_cases h_edge : ∃ c ∈ S, ∃ y ∉ S, G.Adj c y
    · obtain ⟨c, hc_S, y, hy_S, hadj_cy⟩ := h_edge
      have hc_supp : c ∈ C.support := List.mem_toFinset.mp hc_S
      have hy_supp : y ∉ C.support := fun h => hy_S (List.mem_toFinset.mpr h)
      let C' := C.rotate c hc_supp
      have hC'_cycle : C'.IsCycle := Walk.isCycle_rotate hc_supp |>.mpr hC_cycle
      have hC'_len : C'.length = C.length := Walk.length_rotate C c hc_supp
      have hC'_not_nil : ¬ C'.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
      have hC'_nodup : C'.support.dropLast.Nodup := by
        have h_tail_nodup := hC'_cycle.support_nodup
        have h_perm := Walk.tail_support_perm_dropLast_support C'
        rwa [h_perm.nodup_iff] at h_tail_nodup
      have hdrop_path : C'.dropLast.IsPath := by
        rw [Walk.isPath_def, Walk.support_dropLast hC'_not_nil]
        exact hC'_nodup
      have hy_not_drop : y ∉ C'.dropLast.support := by
        rw [Walk.support_dropLast hC'_not_nil]
        intro hy_drop
        have : y ∈ C'.support := List.mem_of_mem_dropLast hy_drop
        have : y ∈ C.support := (Walk.mem_support_rotate_iff C c hc_supp).mp this
        exact hy_supp this
      let Q := C'.dropLast.cons hadj_cy.symm
      have hQ_path : Q.IsPath := by
        rw [Walk.isPath_def, Walk.support_cons, List.nodup_cons]
        exact ⟨hy_not_drop, hdrop_path.support_nodup⟩
      have hQ_len : Q.length = p.length + 1 := by
        simp only [Q, Walk.length_cons, Walk.length_dropLast, hC'_len, hC_len_eq]
        omega
      have hlen_max := hmax Q hQ_path
      omega
    · have h_no_edge : ∀ c ∈ S, ∀ y ∉ S, ¬ G.Adj c y := by
        intro c hc y hy hadj
        exact h_edge ⟨c, hc, y, hy, hadj⟩
      have hu_S : u ∈ S := List.mem_toFinset.mpr C.start_mem_support
      have hore_uw := hore u w (by rintro rfl; exact hw hu_S) (h_no_edge u hu_S w hw)
      have h_nbr_u : G.neighborFinset u ⊆ S.erase u := by
        intro z hz
        rw [SimpleGraph.mem_neighborFinset] at hz
        simp only [Finset.mem_erase]
        refine ⟨hz.ne.symm, ?_⟩
        by_contra hz_not
        have := h_no_edge u hu_S z hz_not
        exact this hz

      have hdeg_u : G.degree u ≤ S.card - 1 := by
        have := Finset.card_le_card h_nbr_u
        rw [Finset.card_erase_of_mem hu_S] at this
        exact this
      have h_nbr_w : G.neighborFinset w ⊆ (Finset.univ \ S).erase w := by
        intro z hz
        rw [SimpleGraph.mem_neighborFinset] at hz
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and]
        refine ⟨hz.ne.symm, ?_⟩
        intro hz_S
        have := h_no_edge z hz_S w hw
        exact this hz.symm
      have hdeg_w : G.degree w ≤ (Fintype.card V - S.card) - 1 := by
        have := Finset.card_le_card h_nbr_w
        rw [Finset.card_erase_of_mem] at this
        · rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at this
          exact this
        · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact hw
      have hu_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨u, hu_S⟩
      have hw_lt : S.card < Fintype.card V := by
        have : S.card ≤ (Finset.univ.erase w).card := Finset.card_le_card (by
          intro z hz
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          rintro rfl
          exact hw hz)
        rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ] at this
        omega
      omega
  refine ⟨u, C, ?_⟩
  exact Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hC_cycle, hC_len_card⟩


/-- Corollary: Dirac's Theorem (1952). -/
theorem dirac_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdirac : ∀ v : V, (Fintype.card V + 1) / 2 ≤ G.degree v) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := by
  apply ore_hamiltonian G hn
  intro u v huv hadj
  have hu := hdirac u
  have hv := hdirac v
  omega

section PathHelpers

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every Hamiltonian cycle yields a Hamiltonian path by dropping the last edge. -/
lemma isHamiltonian_dropLast_of_isHamiltonianCycle {G : SimpleGraph V} {v : V} {C : G.Walk v v}
    (hC : C.IsHamiltonianCycle) :
    C.dropLast.IsHamiltonian := by
  have hC_not_nil : ¬ C.Nil := hC.isCycle.not_nil
  have hC_supp : C.support.dropLast = C.dropLast.support := (Walk.support_dropLast hC_not_nil).symm
  have hC_perm : C.support.tail ~ C.support.dropLast := Walk.tail_support_perm_dropLast_support C
  have h_tail_nodup : C.support.tail.Nodup := hC.isCycle.support_nodup
  have h_drop_nodup : C.dropLast.support.Nodup := by
    rwa [← hC_supp, ← hC_perm.nodup_iff]
  have h_path : C.dropLast.IsPath := by
    rw [Walk.isPath_def]
    exact h_drop_nodup
  rw [h_path.isHamiltonian_iff]
  intro w
  have hw_C : w ∈ C.support := hC.mem_support w
  rw [Walk.mem_support_iff] at hw_C
  rcases hw_C with rfl | hw_tail
  · exact Walk.start_mem_support C.dropLast
  · rw [← hC_supp]
    exact hC_perm.mem_iff.mp hw_tail

/-- Corollary: Hamiltonian Path Theorem under Ore's condition.
    Any graph on n ≥ 3 vertices satisfying deg(u) + deg(v) ≥ n has a Hamiltonian path. -/
theorem ore_hamiltonian_path {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  obtain ⟨v, C, hC⟩ := ore_hamiltonian G hn hore
  refine ⟨v, _, C.dropLast, isHamiltonian_dropLast_of_isHamiltonianCycle hC⟩

/-- Corollary: Dirac Hamiltonian Path Theorem. -/
theorem dirac_hamiltonian_path {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdirac : ∀ v : V, (Fintype.card V + 1) / 2 ≤ G.degree v) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  obtain ⟨v, C, hC⟩ := dirac_hamiltonian G hn hdirac
  refine ⟨v, _, C.dropLast, isHamiltonian_dropLast_of_isHamiltonianCycle hC⟩

end PathHelpers

