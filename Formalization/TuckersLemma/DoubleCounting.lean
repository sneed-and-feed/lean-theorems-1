import Formalization.TuckersLemma.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card

open Finset

/-!
# Combinatorial Double-Counting and Parity Conservation for Tucker's Lemma

This module formalizes the core combinatorial machinery of **Tucker's Lemma** (1945):
1. **Local Face Parity Invariant:**
   For any triangular face `t` with vertex labels in `{±1, ±2}`, if `t` contains no complementary
   edge, then the number of doors on `t` is either `0` or `2` (`doors L t % 2 = 0`).
   Equivalently, if `doors L t % 2 = 1`, then `t` must contain a complementary edge.
2. **Global Double Counting:**
   Summing over all faces, `∑ t ∈ T.faces, doors L t = |E_bd^door| + 2 * |E_int^door|`.
3. **Parity Conservation:**
   Modulo 2 reduction establishes:
   `(∑ t ∈ T.faces, doors L t) % 2 = (T.boundaryEdges.filter (isDoor L)).card % 2`.
4. **Tucker's 2D Existence Theorem (Without `h_witness`):**
   An odd boundary door count forces the existence of a face with an odd door count,
   which in turn forces the existence of a complementary edge in `T.edges`.
-/

namespace TuckersLemma

section DoubleCounting

variable {V : Type*} [DecidableEq V]

/-- Local integer door parity theorem: an odd door count on 3 integers in `{±1, ±2}`
    forces at least one pair to be complementary (`a = -b ∨ a = -c ∨ b = -c`). -/
lemma fin_local_door_odd_has_comp (a b c : ℤ)
    (ha : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2)
    (hb : b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2)
    (hc : c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2)
    (h_odd : ((if ({a, b} : Finset ℤ) = {1, 2} then 1 else 0) +
              (if ({a, c} : Finset ℤ) = {1, 2} then 1 else 0) +
              (if ({b, c} : Finset ℤ) = {1, 2} then 1 else 0)) % 2 = 1) :
    a = -b ∨ a = -c ∨ b = -c := by
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl <;>
  revert h_odd <;> decide

/-- Local integer door parity theorem: no complementary pair implies even door count (0 mod 2). -/
lemma fin_local_door_mod_two_of_no_comp (a b c : ℤ)
    (ha : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2)
    (hb : b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2)
    (hc : c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2)
    (h_nocomp : a ≠ -b ∧ a ≠ -c ∧ b ≠ -c) :
    ((if ({a, b} : Finset ℤ) = {1, 2} then 1 else 0) +
     (if ({a, c} : Finset ℤ) = {1, 2} then 1 else 0) +
     (if ({b, c} : Finset ℤ) = {1, 2} then 1 else 0)) % 2 = 0 := by
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  rcases hc with rfl | rfl | rfl | rfl <;>
  revert h_nocomp <;> decide

lemma triangle_edges_eq {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v, w} : Finset V).powerset.filter (fun s => s.card = 2) = {{u, v}, {u, w}, {v, w}} := by
  ext s; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hcard⟩
    rcases Finset.card_eq_two.mp hcard with ⟨x, y, _, rfl⟩
    have hx : x ∈ ({u, v, w} : Finset V) := hsub (by simp)
    have hy : y ∈ ({u, v, w} : Finset V) := hsub (by simp)
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all [Finset.pair_comm]
  · rintro (rfl | rfl | rfl) <;> simp_all

lemma distinct_edges {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v} : Finset V) ∉ ({{u, w}, {v, w}} : Finset (Finset V)) ∧
    ({u, w} : Finset V) ∉ ({{v, w}} : Finset (Finset V)) ∧
    ({u, v} : Finset V) ≠ ({u, w} : Finset V) ∧
    ({u, v} : Finset V) ≠ ({v, w} : Finset V) ∧
    ({u, w} : Finset V) ≠ ({v, w} : Finset V) := by
  have h1 : ({u, v} : Finset V) ≠ {u, w} := fun h => by have := Finset.ext_iff.mp h v; clear h; simp_all
  have h2 : ({u, v} : Finset V) ≠ {v, w} := fun h => by have := Finset.ext_iff.mp h u; clear h; simp_all
  have h3 : ({u, w} : Finset V) ≠ {v, w} := fun h => by have := Finset.ext_iff.mp h u; clear h; simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]
  exact ⟨⟨h1, h2⟩, h3, h1, h2, h3⟩

lemma doors_eq {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (L : V → ℤ) :
    doors L {u, v, w} =
    (if ({L u, L v} : Finset ℤ) = {1, 2} then 1 else 0) +
    (if ({L u, L w} : Finset ℤ) = {1, 2} then 1 else 0) +
    (if ({L v, L w} : Finset ℤ) = {1, 2} then 1 else 0) := by
  dsimp [doors]
  have h_filter : ({u, v, w} : Finset V).powerset.filter (isDoor L) =
      (({u, v, w} : Finset V).powerset.filter (fun e => e.card = 2)).filter (fun e => e.image L = {1, 2}) := by
    ext e; simp only [mem_filter, mem_powerset, isDoor, and_assoc]
  have ⟨h_disj1, h_disj2, _, _, _⟩ := distinct_edges huv huw hvw
  rw [h_filter, triangle_edges_eq huv huw hvw, card_filter,
      sum_insert h_disj1, sum_insert h_disj2, sum_singleton]
  simp only [image_insert, image_singleton]
  omega

lemma exists_comp_in_face (L : V → ℤ) (t : Finset V) (ht_card : t.card = 3)
    (h_range : ∀ v ∈ t, L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2)
    (h_odd : doors L t % 2 = 1) :
    ∃ e ⊆ t, e.card = 2 ∧ IsComplementaryEdge L e := by
  rcases card_eq_three.mp ht_card with ⟨u, v, w, huv, huw, hvw, rfl⟩
  rw [doors_eq huv huw hvw L] at h_odd
  have hu : L u = 1 ∨ L u = -1 ∨ L u = 2 ∨ L u = -2 := h_range u (by simp)
  have hv : L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2 := h_range v (by simp)
  have hw : L w = 1 ∨ L w = -1 ∨ L w = 2 ∨ L w = -2 := h_range w (by simp)
  rcases fin_local_door_odd_has_comp (L u) (L v) (L w) hu hv hw h_odd with h | h | h
  · refine ⟨{u, v}, ?_, card_pair huv, u, v, by simp, by simp, huv, h⟩
    intro x; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl) <;> simp
  · refine ⟨{u, w}, ?_, card_pair huw, u, w, by simp, by simp, huw, h⟩
    intro x; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl) <;> simp
  · refine ⟨{v, w}, ?_, card_pair hvw, v, w, by simp, by simp, hvw, h⟩
    intro x; simp only [mem_insert, mem_singleton]; rintro (rfl | rfl) <;> simp

lemma sum_boundary_doors (T : EdgePseudomanifold2D V) (L : V → ℤ) :
    (∑ e ∈ T.boundaryEdges, if isDoor L e then (T.incidentFaces e).card else 0) =
    (T.boundaryEdges.filter (isDoor L)).card := by
  rw [card_filter]
  refine sum_congr rfl (fun e he => ?_)
  have : (T.incidentFaces e).card = 1 := (mem_filter.mp he).2
  split_ifs <;> omega

lemma sum_interior_doors (T : EdgePseudomanifold2D V) (L : V → ℤ) :
    (∑ e ∈ T.interiorEdges, if isDoor L e then (T.incidentFaces e).card else 0) =
    2 * (T.interiorEdges.filter (isDoor L)).card := by
  rw [card_filter, mul_sum]
  refine sum_congr rfl (fun e he => ?_)
  have : (T.incidentFaces e).card = 2 := (mem_filter.mp he).2
  split_ifs <;> omega

/-- The total door count across all faces equals boundary doors plus twice interior doors. -/
theorem double_counting_doors (T : EdgePseudomanifold2D V) (L : V → ℤ) :
    (∑ t ∈ T.faces, doors L t) =
    (T.boundaryEdges.filter (isDoor L)).card + 2 * (T.interiorEdges.filter (isDoor L)).card := by
  have h_door_sum (t : Finset V) (ht : t ∈ T.faces) :
      doors L t = ∑ e ∈ T.edges, if e ⊆ t ∧ isDoor L e then 1 else 0 := by
    dsimp [doors]
    have h_sub : (t.powerset.filter (isDoor L)) =
        (T.edges.filter (fun e => e ⊆ t ∧ isDoor L e)) := by
      ext e
      simp only [mem_filter, mem_powerset]
      refine ⟨fun ⟨he_sub, he_door⟩ => ⟨?_, he_sub, he_door⟩, fun ⟨_, he_sub, he_door⟩ => ⟨he_sub, he_door⟩⟩
      dsimp [EdgePseudomanifold2D.edges]
      rw [mem_biUnion]
      exact ⟨t, ht, by simp [mem_filter, mem_powerset, he_sub, he_door.1]⟩
    rw [h_sub, card_filter]
  have h_edge_term (e : Finset V) :
      (∑ t ∈ T.faces, if e ⊆ t ∧ isDoor L e then 1 else 0) =
      if isDoor L e then (T.incidentFaces e).card else 0 := by
    dsimp [EdgePseudomanifold2D.incidentFaces]
    split_ifs with h_door
    · rw [card_filter]; apply sum_congr rfl; intro t _; simp [h_door]
    · exact sum_eq_zero (fun t _ => by simp [h_door])
  rw [sum_congr rfl h_door_sum, sum_comm, sum_congr rfl (fun e _ => h_edge_term e),
      T.edges_eq_boundary_union_interior, sum_union T.edges_disjoint_boundary_interior,
      sum_boundary_doors, sum_interior_doors]

/-- **Parity Conservation Theorem:**
    The total face door count modulo 2 is identically equal to the number of boundary doors modulo 2. -/
theorem parity_conservation (T : EdgePseudomanifold2D V) (L : V → ℤ) :
    (∑ t ∈ T.faces, doors L t) % 2 = (T.boundaryEdges.filter (isDoor L)).card % 2 := by
  rw [double_counting_doors, Nat.add_mod]
  have : (2 * (T.interiorEdges.filter (isDoor L)).card) % 2 = 0 := by omega
  rw [this, add_zero, Nat.mod_mod]

lemma sum_even_of_all_even {β : Type*} (s : Finset β) (f : β → ℕ)
    (h_even : ∀ x ∈ s, f x % 2 = 0) : (∑ x ∈ s, f x) % 2 = 0 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [sum_cons, Nat.add_mod, h_even a (mem_cons_self a s),
        ih (fun x hx => h_even x (mem_cons_of_mem hx))]

lemma exists_odd_of_sum_odd {β : Type*} (s : Finset β) (f : β → ℕ)
    (h : (∑ x ∈ s, f x) % 2 = 1) : ∃ x ∈ s, f x % 2 = 1 := by
  by_contra! h_all
  have h_sum_even := sum_even_of_all_even s f (fun x hx => by have := h_all x hx; omega)
  omega

/-- **Main 2D Tucker Existence Theorem via genuine double counting parity:**
    If a 2D pseudomanifold has an odd number of boundary doors under a labeling `L : α → {±1, ±2}`,
    then there exists a complementary edge in `T.edges`. -/
theorem tucker_2d_of_odd_boundary (T : EdgePseudomanifold2D V) (L : V → ℤ)
    (h_range : ∀ v, L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2)
    (h_bd_odd : (T.boundaryEdges.filter (isDoor L)).card % 2 = 1) :
    ∃ e ∈ T.edges, IsComplementaryEdge L e := by
  have h_sum_odd : (∑ t ∈ T.faces, doors L t) % 2 = 1 := by rw [parity_conservation, h_bd_odd]
  obtain ⟨t, ht_faces, ht_odd⟩ := exists_odd_of_sum_odd T.faces (doors L) h_sum_odd
  obtain ⟨e, he_sub, he_card, he_comp⟩ :=
    exists_comp_in_face L t (T.face_card t ht_faces) (fun v _ => h_range v) ht_odd
  refine ⟨e, ?_, he_comp⟩
  dsimp [EdgePseudomanifold2D.edges]
  rw [mem_biUnion]
  exact ⟨t, ht_faces, by simp [mem_filter, mem_powerset, he_sub, he_card]⟩

/-- 2D Tucker's Lemma on symmetric triangulations with odd boundary door parity:
    Completely eliminates `h_witness`! -/
theorem symmetric_tucker_2d_of_odd_boundary (T : SymmetricTriangulation2D V) (L : V → ℤ)
    (h_range : ∀ v, L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2)
    (h_bd_odd : (T.boundaryEdges.filter (isDoor L)).card % 2 = 1) :
    ∃ e ∈ T.edges, IsComplementaryEdge L e :=
  tucker_2d_of_odd_boundary T.toEdgePseudomanifold2D L h_range h_bd_odd

end DoubleCounting

end TuckersLemma
