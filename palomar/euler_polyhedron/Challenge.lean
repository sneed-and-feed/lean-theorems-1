import Mathlib.Data.Fintype.Card

/-- A connected planar map constructed inductively via Cauchy's 1813 geometric network operations:
    1. A base polygon with n ≥ 3 sides (n vertices, n edges, 2 faces).
    2. A single vertex (1 vertex, 0 edges, 1 face).
    3. Adding a pendant edge/leaf (attaching a new vertex and edge).
    4. Adding a face-splitting chord (connecting two existing vertices along a face boundary, splitting the face).
-/
inductive PlanarMap : Type where
  | singleVertex : PlanarMap
  | polygon (n : ℕ) (hn : 3 ≤ n) : PlanarMap
  | addPendant (M : PlanarMap) : PlanarMap
  | addFaceChord (M : PlanarMap) : PlanarMap
deriving DecidableEq, Repr

namespace PlanarMap

/-- Number of vertices in a planar map. -/
def vertexCount : PlanarMap → ℕ
  | singleVertex => 1
  | polygon n _ => n
  | addPendant M => M.vertexCount + 1
  | addFaceChord M => M.vertexCount

/-- Number of edges in a planar map. -/
def edgeCount : PlanarMap → ℕ
  | singleVertex => 0
  | polygon n _ => n
  | addPendant M => M.edgeCount + 1
  | addFaceChord M => M.edgeCount + 1

/-- Number of faces in a planar map (including the exterior unbounded face). -/
def faceCount : PlanarMap → ℕ
  | singleVertex => 1
  | polygon _ _ => 2
  | addPendant M => M.faceCount
  | addFaceChord M => M.faceCount + 1

/-- Euler characteristic of a planar map: χ(M) = V - E + F. -/
def eulerChar (M : PlanarMap) : ℤ :=
  (M.vertexCount : ℤ) - (M.edgeCount : ℤ) + (M.faceCount : ℤ)

end PlanarMap

/-- **Euler's Polyhedron Formula (1758, Wiedijk #13)**:
    For any inductively generated connected planar map, $V - E + F = 2$. -/
theorem euler_polyhedron_formula (M : PlanarMap) : M.eulerChar = 2 := sorry

/-- **Planar Edge Bound (Standard)**:
    For any connected planar map with $V \ge 3$ vertices where every face has degree \ge 3
    (so $3F \le 2E$), the number of edges satisfies $E \le 3V - 6$. -/
theorem planar_edge_bound (M : PlanarMap)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) :
    M.edgeCount ≤ 3 * M.vertexCount - 6 := sorry

/-- **Triangle-Free Planar Edge Bound**:
    For any connected triangle-free planar map with $V \ge 3$ vertices where every face has degree \ge 4
    (so $4F \le 2E$), the number of edges satisfies $E \le 2V - 4$. -/
theorem planar_edge_bound_triangle_free (M : PlanarMap)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) :
    M.edgeCount ≤ 2 * M.vertexCount - 4 := sorry

/-- **Non-Planarity of K₅ on Planar Maps**:
    There is no connected planar map with 5 vertices, 10 edges, and face degree \ge 3. -/
theorem non_planarity_k5 (M : PlanarMap)
    (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) : False := sorry

/-- **Non-Planarity of K₃,₃ on Planar Maps**:
    There is no connected planar map with 6 vertices, 9 edges, and face degree \ge 4. -/
theorem non_planarity_k33 (M : PlanarMap)
    (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) : False := sorry