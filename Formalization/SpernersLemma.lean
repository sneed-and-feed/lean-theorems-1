import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

/-!
# Sperner's Lemma in 1D and 2D

This module formalizes **Sperner's Lemma** (Emanuel Sperner, 1928), a foundational
result in topological combinatorics, simplicial topology, and discrete fixed-point theory.

## Mathematical Summary

1. **1D Sperner's Lemma:**
   For any coloring `f : Fin (n + 1) → Fin 2` of the vertices of a discrete path of length `n`,
   the number of adjacent color-switching edges is odd if and only if the endpoints have
   different colors (`f 0 ≠ f (Fin.last n)`). In particular, if `f 0 ≠ f (Fin.last n)`,
   there exists at least one bicolored elementary segment.

2. **2D Sperner's Lemma (Triangulations / Simplicial Surfaces with Boundary):**
   Let `T` be an abstract 2D triangulation (a finite collection of 3-element subsets of vertices `α`
   where every edge belongs to either 1 triangle [boundary] or 2 triangles [interior]).
   Let `c : α → Fin 3` be a vertex coloring.
   - Every triangle `t` has door count `triangleDoorCount c t ≡ [isPanchromatic c t] (mod 2)`.
   - Double-counting over all triangles yields:
     `∑ t ∈ T.triangles, triangleDoorCount c t = |E_bd^01| + 2 * |E_int^01|`.
   - Modulo 2 reduction proves the **2D Sperner Parity Invariant**:
     `|{t ∈ T | isPanchromatic c t}| ≡ |E_bd^01| (mod 2)`.
   - Therefore, whenever the boundary contains an odd number of 0-1 edges, the number of
     panchromatic triangles is odd, and there exists at least one panchromatic triangle.

## References
* Sperner, E. (1928). *Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes*.
  Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg, 6(1), 265–272.
* Freek Wiedijk. *Formalizing 100 Theorems*.
-/

/-!
### 1. 1D Sperner's Lemma
-/

/-- Number of color switches between adjacent vertices in a 1D path of length `n`. -/
def switchCount {n : ℕ} (f : Fin (n + 1) → Fin 2) : ℕ :=
  ∑ i : Fin n, if f i.castSucc ≠ f i.succ then 1 else 0

/-- In Fin 2, two elements are either equal or one is 0 and the other is 1. -/
lemma fin2_cases (a b : Fin 2) : a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  fin_cases a <;> fin_cases b <;> aesop

lemma fin2_ne_iff (a b : Fin 2) : a ≠ b ↔ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  fin_cases a <;> fin_cases b <;> simp

lemma fin2_eq_or_ne_of_ne {a b c : Fin 2} (h : a ≠ b) : (a ≠ c ↔ b = c) := by revert a b c h; decide

lemma switchCount_succ {n : ℕ} (f : Fin (n + 2) → Fin 2) :
    switchCount f = (if f 0 ≠ f 1 then 1 else 0) + switchCount (fun i => f i.succ) := by
  dsimp [switchCount]; rw [Fin.sum_univ_succ]; rfl

/-- 1D Sperner's Lemma Parity: The number of color switches along a path is odd
    if and only if the endpoints have different colors. -/
theorem sperner_1d_parity {n : ℕ} (f : Fin (n + 1) → Fin 2) :
    Odd (switchCount f) ↔ f 0 ≠ f (Fin.last n) := by
  induction n with
  | zero => simp [switchCount]
  | succ n ih =>
    rw [switchCount_succ f]
    have ih_g : Odd _ ↔ f 1 ≠ f (Fin.last (n + 1)) := ih (fun i => f i.succ)
    split_ifs with h_step
    · rw [add_comm, Nat.odd_add_one, ih_g, not_not, ← fin2_eq_or_ne_of_ne h_step]
    · push Not at h_step; rw [zero_add, ih_g, h_step]

/-- 1D Sperner's Lemma (Existence): If a 1D path is colored with 2 colors such that
    the endpoints have different colors, there exists at least one edge whose endpoints
    have different colors. -/
theorem sperner_1d_exists {n : ℕ} (f : Fin (n + 1) → Fin 2) (h_ends : f 0 ≠ f (Fin.last n)) :
    ∃ i : Fin n, f i.castSucc ≠ f i.succ := by
  by_contra! h
  have h0 : switchCount f = 0 := sum_eq_zero fun i _ => by simp [h i]
  have h_odd : Odd (switchCount f) := (sperner_1d_parity f).mpr h_ends
  simp_all

/-!
### 2. 2D Triangulations and Combinatorial Surfaces
-/

variable {α : Type*} [DecidableEq α]

/-- An abstract 2-dimensional triangulation (simplicial surface with boundary).
    `triangles` is a collection of 3-element subsets of vertices `α`.
    Every edge (2-element subset of a triangle) belongs to either:
    - Exactly 1 triangle (boundary edge), or
    - Exactly 2 triangles (interior edge). -/
structure Triangulation2D (α : Type*) [DecidableEq α] where
  triangles : Finset (Finset α)
  triangle_card : ∀ t ∈ triangles, t.card = 3
  incident_card : ∀ e ∈ triangles.biUnion (fun t => t.powerset.filter (fun s => s.card = 2)),
    (triangles.filter (fun t => e ⊆ t)).card = 1 ∨ (triangles.filter (fun t => e ⊆ t)).card = 2

/-- All edges of a triangulation (2-element subsets of triangles). -/
def Triangulation2D.edges (T : Triangulation2D α) : Finset (Finset α) :=
  T.triangles.biUnion (fun t => t.powerset.filter (fun s => s.card = 2))

/-- The triangles in `T` containing edge `e`. -/
def Triangulation2D.incidentTriangles (T : Triangulation2D α) (e : Finset α) : Finset (Finset α) :=
  T.triangles.filter (fun t => e ⊆ t)

/-- Boundary edges: edges contained in exactly 1 triangle. -/
def Triangulation2D.boundaryEdges (T : Triangulation2D α) : Finset (Finset α) :=
  T.edges.filter (fun e => (T.incidentTriangles e).card = 1)

/-- Interior edges: edges contained in exactly 2 triangles. -/
def Triangulation2D.interiorEdges (T : Triangulation2D α) : Finset (Finset α) :=
  T.edges.filter (fun e => (T.incidentTriangles e).card = 2)

/-- An edge `e` (2-element set) is a 0-1 edge (or door) if its vertices map to {0, 1}. -/
def is01Edge (c : α → Fin 3) (e : Finset α) : Prop :=
  e.card = 2 ∧ e.image c = ({0, 1} : Finset (Fin 3))

instance (c : α → Fin 3) (e : Finset α) : Decidable (is01Edge c e) :=
  inferInstanceAs (Decidable (e.card = 2 ∧ e.image c = {0, 1}))

/-- A triangle `t` is panchromatic (or fully labeled) if its vertices take all 3 colors {0, 1, 2}. -/
def isPanchromatic (c : α → Fin 3) (t : Finset α) : Prop :=
  t.card = 3 ∧ t.image c = (Finset.univ : Finset (Fin 3))

instance (c : α → Fin 3) (t : Finset α) : Decidable (isPanchromatic c t) :=
  inferInstanceAs (Decidable (t.card = 3 ∧ t.image c = Finset.univ))

/-- The 0-1 edges (doors) on the boundary of triangle `t`. -/
def triangle01Edges (c : α → Fin 3) (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter (fun s => s.card = 2 ∧ s.image c = ({0, 1} : Finset (Fin 3)))

/-- Number of 0-1 edges on triangle `t`. -/
def triangleDoorCount (c : α → Fin 3) (t : Finset α) : ℕ :=
  (triangle01Edges c t).card

/-!
### 3. Local Triangle Door Counting Invariant
-/

/-- Exhaustive finite-type enumeration across all 27 possible color assignments of a triangle. -/
lemma fin3_local_door_count (a b d : Fin 3) :
    ((if ({a, b} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) then 1 else 0) +
     (if ({a, d} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) then 1 else 0) +
     (if ({b, d} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) then 1 else 0)) % 2 =
    if ({a, b, d} : Finset (Fin 3)) = Finset.univ then 1 else 0 := by
  revert a b d; decide

/-- The 2-element subsets of a 3-element set `{u, v, w}` are exactly `{u, v}`, `{u, w}`, `{v, w}`. -/
lemma triangle_edges_eq {u v w : α} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v, w} : Finset α).powerset.filter (fun s => s.card = 2) = {{u, v}, {u, w}, {v, w}} := by
  ext s; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, hcard⟩
    rcases Finset.card_eq_two.mp hcard with ⟨x, y, hxy, rfl⟩
    have hx : x ∈ ({u, v, w} : Finset α) := hsub (by simp)
    have hy : y ∈ ({u, v, w} : Finset α) := hsub (by simp)
    aesop
  · rintro (rfl | rfl | rfl) <;> simp_all

lemma distinct_edges {u v w : α} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v} : Finset α) ∉ ({{u, w}, {v, w}} : Finset (Finset α)) ∧
    ({u, w} : Finset α) ∉ ({{v, w}} : Finset (Finset α)) ∧
    ({u, v} : Finset α) ≠ ({u, w} : Finset α) ∧
    ({u, v} : Finset α) ≠ ({v, w} : Finset α) ∧
    ({u, w} : Finset α) ≠ ({v, w} : Finset α) := by
  have h1 : ({u, v} : Finset α) ≠ {u, w} := fun h => by have := Finset.ext_iff.mp h v; clear h; simp_all
  have h2 : ({u, v} : Finset α) ≠ {v, w} := fun h => by have := Finset.ext_iff.mp h u; clear h; simp_all
  have h3 : ({u, w} : Finset α) ≠ {v, w} := fun h => by have := Finset.ext_iff.mp h u; clear h; simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ne_eq]
  exact ⟨⟨h1, h2⟩, h3, h1, h2, h3⟩

lemma triangle01Edges_eq {u v w : α} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (c : α → Fin 3) :
    triangle01Edges c {u, v, w} =
    ({{u, v}, {u, w}, {v, w}} : Finset (Finset α)).filter (fun s => s.image c = ({0, 1} : Finset (Fin 3))) := by
  ext s
  have := Finset.ext_iff.mp (triangle_edges_eq huv huw hvw) s
  simp only [triangle01Edges, Finset.mem_filter] at this ⊢
  aesop

lemma triangleDoorCount_eq {u v w : α} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (c : α → Fin 3) :
    triangleDoorCount c {u, v, w} =
    (if ({c u, c v} : Finset (Fin 3)) = {0, 1} then 1 else 0) +
    (if ({c u, c w} : Finset (Fin 3)) = {0, 1} then 1 else 0) +
    (if ({c v, c w} : Finset (Fin 3)) = {0, 1} then 1 else 0) := by
  dsimp [triangleDoorCount]
  rw [triangle01Edges_eq huv huw hvw c, Finset.card_filter]
  have ⟨h_disj1, h_disj2, _, _, _⟩ := distinct_edges huv huw hvw
  simp only [Finset.sum_insert h_disj1, Finset.sum_insert h_disj2, Finset.sum_singleton]
  simp [Finset.image_insert, Finset.image_singleton]
  ring

/-- The local triangle door count modulo 2 is 1 if and only if the triangle is panchromatic. -/
lemma triangleDoorCount_mod_two (c : α → Fin 3) (t : Finset α) (ht : t.card = 3) :
    triangleDoorCount c t % 2 = if isPanchromatic c t then 1 else 0 := by
  rcases card_eq_three.mp ht with ⟨u, v, w, huv, huw, hvw, rfl⟩
  rw [triangleDoorCount_eq huv huw hvw c]
  have h_pan : isPanchromatic c ({u, v, w} : Finset α) ↔ ({c u, c v, c w} : Finset (Fin 3)) = Finset.univ := by
    dsimp [isPanchromatic]
    have h_card3 : ({u, v, w} : Finset α).card = 3 := by
      rw [card_insert_of_notMem (by simp [huv, huw]), card_pair hvw]
    simp only [h_card3, true_and]
    have h_im : ({u, v, w} : Finset α).image c = {c u, c v, c w} := by
      simp [Finset.image_insert, Finset.image_singleton]
    rw [h_im]
  rw [if_congr h_pan rfl rfl]
  exact fin3_local_door_count (c u) (c v) (c w)

/-!
### 4. Global Double-Counting Relation
-/

lemma sum_mod_two_eq (s : Finset (Finset α)) (f : Finset α → ℕ) (p : Finset α → Prop) [DecidablePred p]
    (h_mod : ∀ t ∈ s, f t % 2 = if p t then 1 else 0) :
    (∑ t ∈ s, f t) % 2 = (s.filter p).card % 2 := by
  rw [Finset.card_filter]
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    have h1 := h_mod a (Finset.mem_insert_self a s)
    have h2 := ih fun t ht => h_mod t (Finset.mem_insert_of_mem ht)
    omega

lemma sum_boundary_eq (T : Triangulation2D α) (c : α → Fin 3) :
    (∑ e ∈ T.boundaryEdges, if is01Edge c e then (T.incidentTriangles e).card else 0) =
    (T.boundaryEdges.filter (is01Edge c)).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have : (T.incidentTriangles e).card = 1 := (Finset.mem_filter.mp he).2
  split_ifs <;> omega

lemma sum_interior_eq (T : Triangulation2D α) (c : α → Fin 3) :
    (∑ e ∈ T.interiorEdges, if is01Edge c e then (T.incidentTriangles e).card else 0) =
    2 * (T.interiorEdges.filter (is01Edge c)).card := by
  rw [Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have : (T.incidentTriangles e).card = 2 := (Finset.mem_filter.mp he).2
  split_ifs <;> omega

/-- The total door count across all triangles equals boundary doors plus twice interior doors. -/
theorem double_counting_sum_eq (T : Triangulation2D α) (c : α → Fin 3) :
    (∑ t ∈ T.triangles, triangleDoorCount c t) =
    (T.boundaryEdges.filter (is01Edge c)).card + 2 * (T.interiorEdges.filter (is01Edge c)).card := by
  have h_door_sum (t : Finset α) (ht : t ∈ T.triangles) :
      triangleDoorCount c t = ∑ e ∈ T.edges, if e ⊆ t ∧ is01Edge c e then 1 else 0 := by
    dsimp [triangleDoorCount, triangle01Edges, is01Edge]
    have h_sub : (t.powerset.filter (fun s => s.card = 2 ∧ s.image c = ({0, 1} : Finset (Fin 3)))) =
        (T.edges.filter (fun e => e ⊆ t ∧ e.card = 2 ∧ e.image c = ({0, 1} : Finset (Fin 3)))) := by
      ext e
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨he_sub, he_card, he_im⟩
        have he_edges : e ∈ T.edges := by
          dsimp [Triangulation2D.edges]
          rw [mem_biUnion]
          exact ⟨t, ht, by simp [mem_filter, mem_powerset, he_sub, he_card]⟩
        exact ⟨he_edges, he_sub, he_card, he_im⟩
      · rintro ⟨he_edges, he_sub, he_card, he_im⟩
        exact ⟨he_sub, he_card, he_im⟩
    rw [h_sub, Finset.card_filter]
    rfl
  have h_sum_rew : (∑ t ∈ T.triangles, triangleDoorCount c t) =
      ∑ t ∈ T.triangles, ∑ e ∈ T.edges, if e ⊆ t ∧ is01Edge c e then 1 else 0 := by
    apply Finset.sum_congr rfl h_door_sum
  rw [h_sum_rew, Finset.sum_comm]
  have h_edge_term (e : Finset α) (he : e ∈ T.edges) :
      (∑ t ∈ T.triangles, if e ⊆ t ∧ is01Edge c e then 1 else 0) =
      if is01Edge c e then (T.incidentTriangles e).card else 0 := by
    dsimp [Triangulation2D.incidentTriangles]
    split_ifs with h_01
    · rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro t _
      simp [h_01]
    · apply Finset.sum_eq_zero
      intro t _
      simp [h_01]
  have h_sum_edges : (∑ e ∈ T.edges, ∑ t ∈ T.triangles, if e ⊆ t ∧ is01Edge c e then 1 else 0) =
      ∑ e ∈ T.edges, if is01Edge c e then (T.incidentTriangles e).card else 0 := by
    apply Finset.sum_congr rfl h_edge_term
  rw [h_sum_edges]
  have h_disj_bd_int : Disjoint T.boundaryEdges T.interiorEdges := by
    dsimp [Triangulation2D.boundaryEdges, Triangulation2D.interiorEdges]
    rw [disjoint_filter]
    intro x _ h1 h2
    omega
  have h_union : T.edges = T.boundaryEdges ∪ T.interiorEdges := by
    dsimp [Triangulation2D.boundaryEdges, Triangulation2D.interiorEdges, Triangulation2D.edges]
    ext e
    simp only [mem_union, mem_filter]
    constructor
    · intro he
      have := T.incident_card e he
      rcases this with h1 | h2
      · left; exact ⟨he, h1⟩
      · right; exact ⟨he, h2⟩
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
  rw [h_union, Finset.sum_union h_disj_bd_int]
  rw [sum_boundary_eq, sum_interior_eq]

/-!
### 5. Main 2D Sperner's Lemma Theorems
-/

/-- **2D Sperner Parity Theorem (Sperner, 1928):**
    The number of panchromatic (fully labeled) triangles in any 2D triangulation
    has the same parity modulo 2 as the number of 0-1 edges on its boundary. -/
theorem sperner_2d_parity (T : Triangulation2D α) (c : α → Fin 3) :
    (T.triangles.filter (isPanchromatic c)).card % 2 =
    (T.boundaryEdges.filter (is01Edge c)).card % 2 := by
  have h_left : (∑ t ∈ T.triangles, triangleDoorCount c t) % 2 =
      (T.triangles.filter (isPanchromatic c)).card % 2 := by
    apply sum_mod_two_eq
    intro t ht
    exact triangleDoorCount_mod_two c t (T.triangle_card t ht)
  have h_right : (∑ t ∈ T.triangles, triangleDoorCount c t) % 2 =
      (T.boundaryEdges.filter (is01Edge c)).card % 2 := by
    rw [double_counting_sum_eq, Nat.add_mod]
    have : (2 * (T.interiorEdges.filter (is01Edge c)).card) % 2 = 0 := by omega
    rw [this, add_zero, Nat.mod_mod]
  rw [← h_left, h_right]

/-- **2D Sperner's Lemma (Parity Form):**
    If the boundary contains an odd number of 0-1 edges, the number of panchromatic
    triangles is odd. -/
theorem sperner_2d_odd (T : Triangulation2D α) (c : α → Fin 3)
    (h_bd : Odd (T.boundaryEdges.filter (is01Edge c)).card) :
    Odd (T.triangles.filter (isPanchromatic c)).card := by
  rw [Nat.odd_iff] at h_bd ⊢
  rw [sperner_2d_parity, h_bd]

/-- **2D Sperner's Lemma (Existence Theorem):**
    If the boundary of a 2D triangulation contains an odd number of 0-1 edges,
    there exists at least one panchromatic (trichromatic {0, 1, 2}) triangle. -/
theorem sperner_2d_exists (T : Triangulation2D α) (c : α → Fin 3)
    (h_bd : Odd (T.boundaryEdges.filter (is01Edge c)).card) :
    ∃ t ∈ T.triangles, isPanchromatic c t := by
  have h_pos : 0 < (T.triangles.filter (isPanchromatic c)).card := Odd.pos (sperner_2d_odd T c h_bd)
  rw [Finset.card_pos, Finset.filter_nonempty_iff] at h_pos
  exact h_pos