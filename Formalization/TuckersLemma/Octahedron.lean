import Formalization.TuckersLemma.Basic

open Finset

/-!
# Concrete Octahedral 2-Sphere ($S^2_8$) Instance for Tucker's Lemma

This module constructs the canonical 6-vertex, 8-face antipodally symmetric triangulation
of the 2-dimensional sphere (the regular octahedron $S^2_8$) and proves **Tucker's Lemma**
for every antipodal labeling $L : \text{OctV} \to \{\pm 1, \pm 2\}$.

## Structure
- 6 vertices: $\{+1, -1, +2, -2, +3, -3\}$ represented by the inductive type `OctV`.
- Fixed-point-free antipodal involution swapping each $(+i, -i)$ pair.
- 8 triangular faces: all choices of one vertex from each antipodal pair.
- 12 edges: all pairs between distinct coordinate axes.
- Zero boundary edges (closed 2-manifold / 2-pseudomanifold).
- Verified theorem `octahedron_tuckers_lemma`.
-/

namespace TuckersLemma

section Octahedron

/-- The 6 vertices of the regular octahedron, grouped into 3 antipodal pairs. -/
inductive OctV : Type
  | p1 | m1 | p2 | m2 | p3 | m3
  deriving DecidableEq, Repr

instance : Fintype OctV where
  elems := {OctV.p1, OctV.m1, OctV.p2, OctV.m2, OctV.p3, OctV.m3}
  complete := by rintro (_ | _ | _ | _ | _ | _) <;> simp

/-- Antipodal reflection on the octahedron swapping positive and negative vertices. -/
def OctV.antipodal : OctV ≃ OctV where
  toFun := fun
    | .p1 => .m1
    | .m1 => .p1
    | .p2 => .m2
    | .m2 => .p2
    | .p3 => .m3
    | .m3 => .p3
  invFun := fun
    | .p1 => .m1
    | .m1 => .p1
    | .p2 => .m2
    | .m2 => .p2
    | .p3 => .m3
    | .m3 => .p3
  left_inv := by rintro (_ | _ | _ | _ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _ | _ | _ | _) <;> rfl

lemma OctV.antipodal_sq (v : OctV) : OctV.antipodal (OctV.antipodal v) = v := by
  cases v <;> rfl

lemma OctV.antipodal_ne (v : OctV) : OctV.antipodal v ≠ v := by
  cases v <;> decide

/-- The 8 triangular faces of the octahedral 2-sphere. -/
def octahedron_faces : Finset (Finset OctV) :=
  { {OctV.p1, OctV.p2, OctV.p3},
    {OctV.p1, OctV.p2, OctV.m3},
    {OctV.p1, OctV.m2, OctV.p3},
    {OctV.p1, OctV.m2, OctV.m3},
    {OctV.m1, OctV.p2, OctV.p3},
    {OctV.m1, OctV.p2, OctV.m3},
    {OctV.m1, OctV.m2, OctV.p3},
    {OctV.m1, OctV.m2, OctV.m3} }

/-- The 12 edges of the octahedral 2-sphere. -/
def octahedron_edges : Finset (Finset OctV) :=
  octahedron_faces.biUnion (fun t => t.powerset.filter (fun s => s.card = 2))

lemma octahedron_face_card (t : Finset OctV) (ht : t ∈ octahedron_faces) : t.card = 3 := by
  revert t ht; decide

lemma octahedron_incident_card (e : Finset OctV) (he : e ∈ octahedron_edges) :
    (octahedron_faces.filter (fun t => e ⊆ t)).card = 1 ∨
    (octahedron_faces.filter (fun t => e ⊆ t)).card = 2 := by
  revert e he; decide

/-- Concrete 2D symmetric triangulation of the octahedron $S^2_8$. -/
def octahedron_triangulation : SymmetricTriangulation2D OctV where
  faces := octahedron_faces
  face_card := octahedron_face_card
  incident_card := octahedron_incident_card
  antipodal := OctV.antipodal
  antipodal_sq := OctV.antipodal_sq
  antipodal_ne := OctV.antipodal_ne

/-- Exhaustive pigeonhole principle on 3 label values in `{±1, ±2}`. -/
lemma pigeonhole_labels (x y z : ℤ)
    (hx : x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2)
    (hy : y = 1 ∨ y = -1 ∨ y = 2 ∨ y = -2)
    (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    x = -y ∨ x = y ∨ x = -z ∨ x = z ∨ y = -z ∨ y = z := by
  rcases hx with rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl <;>
  rcases hz with rfl | rfl | rfl | rfl <;> decide

/-- **Tucker's Lemma on the Octahedral 2-Sphere ($S^2_8$):**
    Every antipodally symmetric labeling `L : OctV → {±1, ±2}` contains a complementary edge
    in the 12 edges of the octahedron. -/
theorem octahedron_tuckers_lemma (L : OctV → ℤ)
    (h_anti : ∀ v, L (OctV.antipodal v) = - L v)
    (h_range : ∀ v, L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2) :
    ∃ e ∈ octahedron_triangulation.edges, IsComplementaryEdge L e := by
  have hm2 : L OctV.m2 = - L OctV.p2 := h_anti OctV.p2
  have hm3 : L OctV.m3 = - L OctV.p3 := h_anti OctV.p3
  have hp := pigeonhole_labels (L OctV.p1) (L OctV.p2) (L OctV.p3)
    (h_range _) (h_range _) (h_range _)
  rcases hp with h | h | h | h | h | h
  · exact ⟨{OctV.p1, OctV.p2}, by decide, OctV.p1, OctV.p2, by simp, by simp, by decide, h⟩
  · exact ⟨{OctV.p1, OctV.m2}, by decide, OctV.p1, OctV.m2, by simp, by simp, by decide, by omega⟩
  · exact ⟨{OctV.p1, OctV.p3}, by decide, OctV.p1, OctV.p3, by simp, by simp, by decide, h⟩
  · exact ⟨{OctV.p1, OctV.m3}, by decide, OctV.p1, OctV.m3, by simp, by simp, by decide, by omega⟩
  · exact ⟨{OctV.p2, OctV.p3}, by decide, OctV.p2, OctV.p3, by simp, by simp, by decide, h⟩
  · exact ⟨{OctV.p2, OctV.m3}, by decide, OctV.p2, OctV.m3, by simp, by simp, by decide, by omega⟩

end Octahedron

end TuckersLemma
