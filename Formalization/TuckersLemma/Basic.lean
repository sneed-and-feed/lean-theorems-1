import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Equiv.Basic

open Finset

/-!
# 2D Symmetric Triangulations and Pseudomanifolds for Tucker's Lemma

This module defines the basic combinatorial structures for **Tucker's Lemma** (1945):
- 2-dimensional edge-pseudomanifolds with boundary
- Antipodally symmetric triangulations
- Door predicates and door counting functions
- Complementary edges under integer sign labelings
-/

namespace TuckersLemma

section Structures

variable {V : Type*} [DecidableEq V]

/-- An abstract 2-dimensional edge-pseudomanifold with boundary.
    - `faces`: finite collection of 3-element subsets of vertices `V`.
    - Every edge (2-element subset of a face) belongs to either 1 face (boundary) or 2 faces (interior). -/
structure EdgePseudomanifold2D (V : Type*) [DecidableEq V] where
  faces : Finset (Finset V)
  face_card : ∀ t ∈ faces, t.card = 3
  incident_card : ∀ e ∈ faces.biUnion (fun t => t.powerset.filter (fun s => s.card = 2)),
    (faces.filter (fun t => e ⊆ t)).card = 1 ∨ (faces.filter (fun t => e ⊆ t)).card = 2

/-- An abstract 2D antipodally symmetric triangulation.
    Combines an `EdgePseudomanifold2D` structure with an antipodal involution `antipodal : V ≃ V`
    satisfying `antipodal (antipodal v) = v` and `antipodal v ≠ v`. -/
structure SymmetricTriangulation2D (V : Type*) [DecidableEq V] extends EdgePseudomanifold2D V where
  antipodal : V ≃ V
  antipodal_sq : ∀ v, antipodal (antipodal v) = v
  antipodal_ne : ∀ v, antipodal v ≠ v

namespace EdgePseudomanifold2D

/-- All edges (1-simplices) of a 2D pseudomanifold. -/
def edges (T : EdgePseudomanifold2D V) : Finset (Finset V) :=
  T.faces.biUnion (fun t => t.powerset.filter (fun s => s.card = 2))

/-- The faces containing a given edge `e`. -/
def incidentFaces (T : EdgePseudomanifold2D V) (e : Finset V) : Finset (Finset V) :=
  T.faces.filter (fun t => e ⊆ t)

/-- Boundary edges: edges contained in exactly 1 face. -/
def boundaryEdges (T : EdgePseudomanifold2D V) : Finset (Finset V) :=
  T.edges.filter (fun e => (T.incidentFaces e).card = 1)

/-- Interior edges: edges contained in exactly 2 faces. -/
def interiorEdges (T : EdgePseudomanifold2D V) : Finset (Finset V) :=
  T.edges.filter (fun e => (T.incidentFaces e).card = 2)

lemma edges_disjoint_boundary_interior (T : EdgePseudomanifold2D V) :
    Disjoint T.boundaryEdges T.interiorEdges := by
  dsimp [boundaryEdges, interiorEdges]
  rw [disjoint_filter]
  intro _ _ h1 h2
  omega

lemma edges_eq_boundary_union_interior (T : EdgePseudomanifold2D V) :
    T.edges = T.boundaryEdges ∪ T.interiorEdges := by
  dsimp [boundaryEdges, interiorEdges, edges]
  ext e
  simp only [mem_union, mem_filter]
  constructor
  · intro he
    have := T.incident_card e he
    rcases this with h1 | h2
    · left; exact ⟨he, h1⟩
    · right; exact ⟨he, h2⟩
  · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he

end EdgePseudomanifold2D

namespace SymmetricTriangulation2D

/-- Edges of a symmetric triangulation. -/
def edges (T : SymmetricTriangulation2D V) : Finset (Finset V) :=
  T.toEdgePseudomanifold2D.edges

/-- Incident faces of an edge in a symmetric triangulation. -/
def incidentFaces (T : SymmetricTriangulation2D V) (e : Finset V) : Finset (Finset V) :=
  T.toEdgePseudomanifold2D.incidentFaces e

/-- Boundary edges of a symmetric triangulation. -/
def boundaryEdges (T : SymmetricTriangulation2D V) : Finset (Finset V) :=
  T.toEdgePseudomanifold2D.boundaryEdges

/-- Interior edges of a symmetric triangulation. -/
def interiorEdges (T : SymmetricTriangulation2D V) : Finset (Finset V) :=
  T.toEdgePseudomanifold2D.interiorEdges

end SymmetricTriangulation2D

/-- An edge `e` is complementary under labeling `L` if it contains two distinct vertices
    with opposite signs: `L u = - L v`. -/
def IsComplementaryEdge (L : V → ℤ) (e : Finset V) : Prop :=
  ∃ u v, u ∈ e ∧ v ∈ e ∧ u ≠ v ∧ L u = - L v

/-- An edge `e` is a door under labeling `L` if `e` has 2 vertices and maps to `{1, 2}`. -/
def isDoor (L : V → ℤ) (e : Finset V) : Prop :=
  e.card = 2 ∧ e.image L = ({1, 2} : Finset ℤ)

instance (L : V → ℤ) (e : Finset V) : Decidable (isDoor L e) :=
  inferInstanceAs (Decidable (e.card = 2 ∧ e.image L = {1, 2}))

/-- The number of doors on a face `t`. -/
def doors (L : V → ℤ) (t : Finset V) : ℕ :=
  (t.powerset.filter (isDoor L)).card

end Structures

end TuckersLemma
