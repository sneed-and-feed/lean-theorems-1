import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

open Finset

variable {α : Type*} [DecidableEq α]

-- ============================================================================
-- Section 1: Abstract 3D Triangulations
-- ============================================================================

/-- An abstract 3-dimensional face-pseudomanifold with boundary.
    `tetrahedra` is a collection of 4-element subsets of vertices `α`.
    Every 2-face (3-element subset of a tetrahedron) belongs to either:
    - Exactly 1 tetrahedron (boundary face), or
    - Exactly 2 tetrahedra (interior face).
    Note: Sperner's 3D combinatorial parity identity holds intrinsically for all finite face-pseudomanifolds
    with boundary, without requiring full 3-manifold vertex link conditions. -/
structure FacePseudomanifold3D (α : Type*) [DecidableEq α] where
  tetrahedra : Finset (Finset α)
  tetrahedron_card : ∀ t ∈ tetrahedra, t.card = 4
  incident_card : ∀ f ∈ tetrahedra.biUnion (fun t => t.powerset.filter (fun s => s.card = 3)),
    (tetrahedra.filter (fun t => f ⊆ t)).card = 1 ∨ (tetrahedra.filter (fun t => f ⊆ t)).card = 2

/-- All triangular 2-faces of a 3D face-pseudomanifold (3-element subsets of tetrahedra). -/
def FacePseudomanifold3D.faces (T : FacePseudomanifold3D α) : Finset (Finset α) :=
  T.tetrahedra.biUnion (fun t => t.powerset.filter (fun s => s.card = 3))

/-- The tetrahedra containing a given face `f`. -/
def FacePseudomanifold3D.incidentTetrahedra (T : FacePseudomanifold3D α) (f : Finset α) : Finset (Finset α) :=
  T.tetrahedra.filter (fun t => f ⊆ t)

/-- Boundary faces: triangular 2-faces contained in exactly 1 tetrahedron. -/
def FacePseudomanifold3D.boundaryFaces (T : FacePseudomanifold3D α) : Finset (Finset α) :=
  T.faces.filter (fun f => (T.incidentTetrahedra f).card = 1)

/-- Interior faces: triangular 2-faces contained in exactly 2 tetrahedra. -/
def FacePseudomanifold3D.interiorFaces (T : FacePseudomanifold3D α) : Finset (Finset α) :=
  T.faces.filter (fun f => (T.incidentTetrahedra f).card = 2)

-- ============================================================================
-- Section 2: Colorings and Doors
-- ============================================================================

/-- A triangular face is a 0-1-2 face (door) if its vertices map onto {0, 1, 2}. -/
def is012Face (c : α → Fin 4) (f : Finset α) : Prop :=
  f.card = 3 ∧ f.image c = ({0, 1, 2} : Finset (Fin 4))

instance (c : α → Fin 4) (f : Finset α) : Decidable (is012Face c f) :=
  inferInstanceAs (Decidable (f.card = 3 ∧ f.image c = {0, 1, 2}))

/-- A tetrahedron is panchromatic if its 4 vertices take all 4 colors {0, 1, 2, 3}. -/
def isPanchromatic4 (c : α → Fin 4) (t : Finset α) : Prop :=
  t.card = 4 ∧ t.image c = (Finset.univ : Finset (Fin 4))

instance (c : α → Fin 4) (t : Finset α) : Decidable (isPanchromatic4 c t) :=
  inferInstanceAs (Decidable (t.card = 4 ∧ t.image c = Finset.univ))

/-- The 0-1-2 faces on the boundary of a tetrahedron `t`. -/
def tetrahedron012Faces (c : α → Fin 4) (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter (fun s => s.card = 3 ∧ s.image c = ({0, 1, 2} : Finset (Fin 4)))

/-- Number of 0-1-2 faces on a tetrahedron `t`. -/
def tetrahedronDoorCount (c : α → Fin 4) (t : Finset α) : ℕ :=
  (tetrahedron012Faces c t).card

-- ============================================================================
-- Section 3: Local Parity Invariant and Main Theorems
-- ============================================================================

/-- Exhaustive finite-type check across all $4^4 = 256$ color assignments of a tetrahedron. -/
lemma fin4_local_door_count (a b d e : Fin 4) :
    ((if ({a, b, d} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0) +
     (if ({a, b, e} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0) +
     (if ({a, d, e} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0) +
     (if ({b, d, e} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0)) % 2 =
    if ({a, b, d, e} : Finset (Fin 4)) = Finset.univ then 1 else 0 := by
  revert a b d e
  decide

lemma erase_four_first {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    ({a, b, c, d} : Finset α).erase a = {b, c, d} := by
  ext t; simp only [mem_erase, mem_insert, mem_singleton]; aesop

lemma distinct_four_faces {u v w z : α}
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    (({u, v, w, z} : Finset α).powerset.filter (fun s => s.card = 3)) =
    ({{u, v, w}, {u, v, z}, {u, w, z}, {v, w, z}} : Finset (Finset α)) := by
  ext s
  simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
  constructor
  · intro ⟨hsub, hcard⟩
    have h4 : ({u, v, w, z} : Finset α).card = 4 := by
      rw [card_eq_four]
      exact ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, rfl⟩
    have h_diff : (({u, v, w, z} : Finset α) \ s).card = 1 := by
      rw [card_sdiff_of_subset hsub, h4, hcard]
    obtain ⟨x, hx⟩ := card_eq_one.mp h_diff
    have hx_mem : x ∈ ({u, v, w, z} : Finset α) := by
      have : x ∈ ({u, v, w, z} : Finset α) \ s := by rw [hx]; exact mem_singleton_self x
      exact (mem_sdiff.mp this).1
    have hx_not_s : x ∉ s := by
      have : x ∈ ({u, v, w, z} : Finset α) \ s := by rw [hx]; exact mem_singleton_self x
      exact (mem_sdiff.mp this).2
    have hs_eq : s = ({u, v, w, z} : Finset α).erase x := by
      ext y
      rw [mem_erase]
      constructor
      · intro hy
        refine ⟨?_, hsub hy⟩
        rintro rfl
        exact hx_not_s hy
      · rintro ⟨hyx, hy_mem⟩
        by_contra hy_not
        have : y ∈ ({u, v, w, z} : Finset α) \ s := mem_sdiff.mpr ⟨hy_mem, hy_not⟩
        rw [hx, mem_singleton] at this
        exact hyx this
    simp only [mem_insert, mem_singleton] at hx_mem
    rcases hx_mem with hu | hv | hw | hz
    · right; right; right
      rw [hu] at hs_eq
      rw [hs_eq]
      exact erase_four_first huv huw huz
    · right; right; left
      rw [hv] at hs_eq
      rw [hs_eq]
      have : ({u, v, w, z} : Finset α) = {v, u, w, z} := by
        ext t; simp only [mem_insert, mem_singleton]; tauto
      rw [this, erase_four_first huv.symm hvw hvz]
    · right; left
      rw [hw] at hs_eq
      rw [hs_eq]
      have : ({u, v, w, z} : Finset α) = {w, u, v, z} := by
        ext t; simp only [mem_insert, mem_singleton]; tauto
      rw [this, erase_four_first huw.symm hvw.symm hwz]
    · left
      rw [hz] at hs_eq
      rw [hs_eq]
      have : ({u, v, w, z} : Finset α) = {z, u, v, w} := by
        ext t; simp only [mem_insert, mem_singleton]; tauto
      rw [this, erase_four_first huz.symm hvz.symm hwz.symm]
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨by intro x; simp; tauto, ?_⟩
      rw [card_eq_three]
      exact ⟨u, v, w, huv, huw, hvw, rfl⟩
    · refine ⟨by intro x; simp; tauto, ?_⟩
      rw [card_eq_three]
      exact ⟨u, v, z, huv, huz, hvz, rfl⟩
    · refine ⟨by intro x; simp; tauto, ?_⟩
      rw [card_eq_three]
      exact ⟨u, w, z, huw, huz, hwz, rfl⟩
    · refine ⟨by intro x; simp; tauto, ?_⟩
      rw [card_eq_three]
      exact ⟨v, w, z, hvw, hvz, hwz, rfl⟩

lemma distinct_face_elements {u v w z : α}
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ({u, v, w} : Finset α) ∉ ({{u, v, z}, {u, w, z}, {v, w, z}} : Finset (Finset α)) ∧
    ({u, v, z} : Finset α) ∉ ({{u, w, z}, {v, w, z}} : Finset (Finset α)) ∧
    ({u, w, z} : Finset α) ∉ ({{v, w, z}} : Finset (Finset α)) ∧
    ({u, v, w} : Finset α) ≠ ({u, v, z} : Finset α) ∧
    ({u, v, w} : Finset α) ≠ ({u, w, z} : Finset α) ∧
    ({u, v, w} : Finset α) ≠ ({v, w, z} : Finset α) ∧
    ({u, v, z} : Finset α) ≠ ({u, w, z} : Finset α) ∧
    ({u, v, z} : Finset α) ≠ ({v, w, z} : Finset α) ∧
    ({u, w, z} : Finset α) ≠ ({v, w, z} : Finset α) := by
  have h1 : ({u, v, w} : Finset α) ≠ {u, v, z} := by
    intro h; have : w ∈ ({u, v, z} : Finset α) := by rw [← h]; simp
    simp [huw.symm, hvw.symm, hwz] at this
  have h2 : ({u, v, w} : Finset α) ≠ {u, w, z} := by
    intro h; have : v ∈ ({u, w, z} : Finset α) := by rw [← h]; simp
    simp [huv.symm, hvw, hvz] at this
  have h3 : ({u, v, w} : Finset α) ≠ {v, w, z} := by
    intro h; have : u ∈ ({v, w, z} : Finset α) := by rw [← h]; simp
    simp [huv, huw, huz] at this
  have h4 : ({u, v, z} : Finset α) ≠ {u, w, z} := by
    intro h; have : v ∈ ({u, w, z} : Finset α) := by rw [← h]; simp
    simp [huv.symm, hvw, hvz] at this
  have h5 : ({u, v, z} : Finset α) ≠ {v, w, z} := by
    intro h; have : u ∈ ({v, w, z} : Finset α) := by rw [← h]; simp
    simp [huv, huw, huz] at this
  have h6 : ({u, w, z} : Finset α) ≠ {v, w, z} := by
    intro h; have : u ∈ ({v, w, z} : Finset α) := by rw [← h]; simp
    simp [huv, huw, huz] at this
  refine ⟨?_, ?_, ?_, h1, h2, h3, h4, h5, h6⟩
  · simp only [mem_insert, mem_singleton, not_or]; exact ⟨h1, h2, h3⟩
  · simp only [mem_insert, mem_singleton, not_or]; exact ⟨h4, h5⟩
  · simp only [mem_singleton]; exact h6

lemma card_filter_eq_sum_ite {β : Type*} [DecidableEq β] (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  rw [card_eq_sum_ones, sum_filter]

lemma tetrahedronDoorCount_eq {u v w z : α}
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (c : α → Fin 4) :
    tetrahedronDoorCount c {u, v, w, z} =
    (if ({c u, c v, c w} : Finset (Fin 4)) = {0, 1, 2} then 1 else 0) +
    (if ({c u, c v, c z} : Finset (Fin 4)) = {0, 1, 2} then 1 else 0) +
    (if ({c u, c w, c z} : Finset (Fin 4)) = {0, 1, 2} then 1 else 0) +
    (if ({c v, c w, c z} : Finset (Fin 4)) = {0, 1, 2} then 1 else 0) := by
  dsimp [tetrahedronDoorCount, tetrahedron012Faces]
  have h_faces := distinct_four_faces huv huw huz hvw hvz hwz
  have h_filter_pow : (({u, v, w, z} : Finset α).powerset.filter
      (fun s => s.card = 3 ∧ s.image c = ({0, 1, 2} : Finset (Fin 4)))) =
      (({u, v, w, z} : Finset α).powerset.filter (fun s => s.card = 3)).filter
      (fun s => s.image c = ({0, 1, 2} : Finset (Fin 4))) := by
    ext s; simp only [mem_filter, and_assoc]
  rw [h_filter_pow, h_faces]
  rw [card_filter_eq_sum_ite]
  have ⟨h_disj1, h_disj2, h_disj3, _⟩ := distinct_face_elements huv huw huz hvw hvz hwz
  rw [sum_insert h_disj1, sum_insert h_disj2, sum_insert h_disj3, sum_singleton]
  have h_im1 : ({u, v, w} : Finset α).image c = {c u, c v, c w} := by
    simp [Finset.image_insert, Finset.image_singleton]
  have h_im2 : ({u, v, z} : Finset α).image c = {c u, c v, c z} := by
    simp [Finset.image_insert, Finset.image_singleton]
  have h_im3 : ({u, w, z} : Finset α).image c = {c u, c w, c z} := by
    simp [Finset.image_insert, Finset.image_singleton]
  have h_im4 : ({v, w, z} : Finset α).image c = {c v, c w, c z} := by
    simp [Finset.image_insert, Finset.image_singleton]
  rw [h_im1, h_im2, h_im3, h_im4]
  ring

/-- Local door count parity on any 4-element tetrahedron. -/
lemma tetrahedronDoorCount_mod_two (c : α → Fin 4) (t : Finset α) (ht : t.card = 4) :
    tetrahedronDoorCount c t % 2 = if isPanchromatic4 c t then 1 else 0 := by
  rcases card_eq_four.mp ht with ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, rfl⟩
  rw [tetrahedronDoorCount_eq huv huw huz hvw hvz hwz c]
  have h_pan : isPanchromatic4 c ({u, v, w, z} : Finset α) ↔
      ({c u, c v, c w, c z} : Finset (Fin 4)) = Finset.univ := by
    dsimp [isPanchromatic4]
    have h_card4 : ({u, v, w, z} : Finset α).card = 4 := by
      rw [card_eq_four]
      exact ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, rfl⟩
    simp only [h_card4, true_and]
    have h_im : ({u, v, w, z} : Finset α).image c = {c u, c v, c w, c z} := by
      simp [Finset.image_insert, Finset.image_singleton]
    rw [h_im]
  rw [if_congr h_pan rfl rfl]
  exact fin4_local_door_count (c u) (c v) (c w) (c z)

lemma sum_mod_two_eq_3d {β : Type*} [DecidableEq β] (s : Finset β) (f : β → ℕ) (p : β → Prop) [DecidablePred p]
    (h_mod : ∀ x ∈ s, f x % 2 = if p x then 1 else 0) :
    (∑ x ∈ s, f x) % 2 = (s.filter p).card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.sum_insert has, Finset.filter_insert]
    have ha := h_mod a (Finset.mem_insert_self a s)
    have ih_s := ih (fun t ht => h_mod t (Finset.mem_insert_of_mem ht))
    split_ifs with hp
    · rw [Finset.card_insert_of_notMem (by simp [has])]
      have h_add : (f a + ∑ t ∈ s, f t) % 2 = (f a % 2 + (∑ t ∈ s, f t) % 2) % 2 := Nat.add_mod (f a) _ 2
      simp only [hp, ite_true] at ha
      rw [h_add, ha, ih_s]
      omega
    · have h_add : (f a + ∑ t ∈ s, f t) % 2 = (f a % 2 + (∑ t ∈ s, f t) % 2) % 2 := Nat.add_mod (f a) _ 2
      simp only [hp, ite_false] at ha
      rw [h_add, ha, ih_s, zero_add, Nat.mod_mod]

lemma sum_boundary_eq_3d (T : FacePseudomanifold3D α) (c : α → Fin 4) :
    (∑ f ∈ T.boundaryFaces, if is012Face c f then (T.incidentTetrahedra f).card else 0) =
    (T.boundaryFaces.filter (is012Face c)).card := by
  have : (∑ f ∈ T.boundaryFaces, if is012Face c f then (T.incidentTetrahedra f).card else 0) =
      ∑ f ∈ T.boundaryFaces, if is012Face c f then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro f hf
    have hf_card : (T.incidentTetrahedra f).card = 1 := (mem_filter.mp hf).2
    rw [hf_card]
  rw [this, ← card_filter_eq_sum_ite]

lemma sum_interior_eq_3d (T : FacePseudomanifold3D α) (c : α → Fin 4) :
    (∑ f ∈ T.interiorFaces, if is012Face c f then (T.incidentTetrahedra f).card else 0) =
    2 * (T.interiorFaces.filter (is012Face c)).card := by
  have : (∑ f ∈ T.interiorFaces, if is012Face c f then (T.incidentTetrahedra f).card else 0) =
      ∑ f ∈ T.interiorFaces, if is012Face c f then 2 else 0 := by
    apply Finset.sum_congr rfl
    intro f hf
    have hf_card : (T.incidentTetrahedra f).card = 2 := (mem_filter.mp hf).2
    rw [hf_card]
  rw [this]
  have h_mul : (∑ f ∈ T.interiorFaces, if is012Face c f then 2 else 0) =
      2 * ∑ f ∈ T.interiorFaces, if is012Face c f then 1 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> ring
  rw [h_mul, ← card_filter_eq_sum_ite]

theorem double_counting_sum_eq_3d (T : FacePseudomanifold3D α) (c : α → Fin 4) :
    (∑ t ∈ T.tetrahedra, tetrahedronDoorCount c t) =
    (T.boundaryFaces.filter (is012Face c)).card + 2 * (T.interiorFaces.filter (is012Face c)).card := by
  have h_door_sum (t : Finset α) (ht : t ∈ T.tetrahedra) :
      tetrahedronDoorCount c t = ∑ f ∈ T.faces, if f ⊆ t ∧ is012Face c f then 1 else 0 := by
    dsimp [tetrahedronDoorCount, tetrahedron012Faces, is012Face]
    have h_sub : (t.powerset.filter (fun s => s.card = 3 ∧ s.image c = ({0, 1, 2} : Finset (Fin 4)))) =
        (T.faces.filter (fun f => f ⊆ t ∧ f.card = 3 ∧ f.image c = ({0, 1, 2} : Finset (Fin 4)))) := by
      ext f
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨hf_sub, hf_card, hf_im⟩
        have hf_faces : f ∈ T.faces := by
          dsimp [FacePseudomanifold3D.faces]
          rw [mem_biUnion]
          exact ⟨t, ht, by simp [mem_filter, mem_powerset, hf_sub, hf_card]⟩
        exact ⟨hf_faces, hf_sub, hf_card, hf_im⟩
      · rintro ⟨hf_faces, hf_sub, hf_card, hf_im⟩
        exact ⟨hf_sub, hf_card, hf_im⟩
    rw [h_sub, card_filter_eq_sum_ite]
    rfl
  have h_sum_rew : (∑ t ∈ T.tetrahedra, tetrahedronDoorCount c t) =
      ∑ t ∈ T.tetrahedra, ∑ f ∈ T.faces, if f ⊆ t ∧ is012Face c f then 1 else 0 := by
    apply Finset.sum_congr rfl h_door_sum
  rw [h_sum_rew, Finset.sum_comm]
  have h_face_term (f : Finset α) (hf : f ∈ T.faces) :
      (∑ t ∈ T.tetrahedra, if f ⊆ t ∧ is012Face c f then 1 else 0) =
      if is012Face c f then (T.incidentTetrahedra f).card else 0 := by
    dsimp [FacePseudomanifold3D.incidentTetrahedra]
    split_ifs with h_012
    · have : (∑ t ∈ T.tetrahedra, if f ⊆ t ∧ is012Face c f then 1 else 0) =
          ∑ t ∈ T.tetrahedra, if f ⊆ t then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        simp [h_012]
      rw [this, ← card_filter_eq_sum_ite]
    · apply Finset.sum_eq_zero
      intro t _
      simp [h_012]
  have h_sum_faces : (∑ f ∈ T.faces, ∑ t ∈ T.tetrahedra, if f ⊆ t ∧ is012Face c f then 1 else 0) =
      ∑ f ∈ T.faces, if is012Face c f then (T.incidentTetrahedra f).card else 0 := by
    apply Finset.sum_congr rfl h_face_term
  rw [h_sum_faces]
  have h_disj_bd_int : Disjoint T.boundaryFaces T.interiorFaces := by
    dsimp [FacePseudomanifold3D.boundaryFaces, FacePseudomanifold3D.interiorFaces]
    rw [disjoint_filter]
    intro x _ h1 h2
    omega
  have h_union : T.faces = T.boundaryFaces ∪ T.interiorFaces := by
    dsimp [FacePseudomanifold3D.boundaryFaces, FacePseudomanifold3D.interiorFaces, FacePseudomanifold3D.faces]
    ext f
    simp only [mem_union, mem_filter]
    constructor
    · intro hf
      have := T.incident_card f hf
      rcases this with h1 | h2
      · left; exact ⟨hf, h1⟩
      · right; exact ⟨hf, h2⟩
    · rintro (⟨hf, _⟩ | ⟨hf, _⟩) <;> exact hf
  rw [h_union, Finset.sum_union h_disj_bd_int]
  rw [sum_boundary_eq_3d, sum_interior_eq_3d]

/-- **3D Sperner Parity Theorem (Sperner 1928):**
    The number of panchromatic tetrahedra in a 3D face-pseudomanifold has the same parity
    modulo 2 as the number of 0-1-2 triangular faces on its boundary. -/
theorem sperner_3d_parity (T : FacePseudomanifold3D α) (c : α → Fin 4) :
    (T.tetrahedra.filter (isPanchromatic4 c)).card % 2 =
    (T.boundaryFaces.filter (is012Face c)).card % 2 := by
  have h_left : (∑ t ∈ T.tetrahedra, tetrahedronDoorCount c t) % 2 =
      (T.tetrahedra.filter (isPanchromatic4 c)).card % 2 := by
    apply sum_mod_two_eq_3d
    intro t ht
    exact tetrahedronDoorCount_mod_two c t (T.tetrahedron_card t ht)
  have h_right : (∑ t ∈ T.tetrahedra, tetrahedronDoorCount c t) % 2 =
      (T.boundaryFaces.filter (is012Face c)).card % 2 := by
    rw [double_counting_sum_eq_3d]
    rw [Nat.add_mod]
    have : (2 * (T.interiorFaces.filter (is012Face c)).card) % 2 = 0 := by omega
    rw [this, add_zero, Nat.mod_mod]
  rw [← h_left, h_right]

/-- **3D Sperner's Lemma (Parity Form):**
    If the boundary contains an odd number of 0-1-2 faces, the number of panchromatic
    tetrahedra is odd. -/
theorem sperner_3d_odd (T : FacePseudomanifold3D α) (c : α → Fin 4)
    (h_bd : Odd (T.boundaryFaces.filter (is012Face c)).card) :
    Odd (T.tetrahedra.filter (isPanchromatic4 c)).card := by
  rw [Nat.odd_iff] at h_bd ⊢
  rw [sperner_3d_parity, h_bd]

/-- **3D Sperner Existence Theorem:**
    Whenever the boundary of a 3D face-pseudomanifold contains an odd number of 0-1-2 faces,
    there exists at least one panchromatic tetrahedron {0, 1, 2, 3}. -/
theorem sperner_3d_exists (T : FacePseudomanifold3D α) (c : α → Fin 4)
    (h_bd : Odd (T.boundaryFaces.filter (is012Face c)).card) :
    ∃ t ∈ T.tetrahedra, isPanchromatic4 c t := by
  have h_odd : Odd (T.tetrahedra.filter (isPanchromatic4 c)).card := sperner_3d_odd T c h_bd
  have h_pos : 0 < (T.tetrahedra.filter (isPanchromatic4 c)).card := Odd.pos h_odd
  rw [Finset.card_pos] at h_pos
  rcases Finset.filter_nonempty_iff.mp h_pos with ⟨t, ht, h_pan⟩
  exact ⟨t, ht, h_pan⟩

