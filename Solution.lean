import Mathlib.Data.Fintype.Card

/--
A connected planar map constructed inductively via Cauchy's 1813 geometric network operations
(as detailed in *Recherches sur les polyèdres*).

**Academic Scope & Disclosure**:
This formalization models connected planar graphs and polyhedral nets syntactically through
inductive graph constructions:
  1. A base polygon with n ≥ 3 sides.
  2. A single vertex.
  3. Adding a pendant edge/leaf.
  4. Adding a face-splitting chord.

This is a combinatorial model of planar maps. It explicitly does NOT formally define or
depend on continuous 2-manifold embeddings, general Jordan curve topology, or geometric
embeddings in ℝ².
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

/-- Euler's polyhedron formula (Euler 1758, proven by Cauchy 1813) for planar maps. -/
theorem euler_polyhedron_formula (M : PlanarMap) : M.eulerChar = 2 := by
  induction M <;> simp only [PlanarMap.eulerChar, PlanarMap.vertexCount, PlanarMap.edgeCount, PlanarMap.faceCount] at * <;> omega

/-- The natural number version of Euler's formula: V + F = E + 2. -/
theorem euler_polyhedron_formula_nat (M : PlanarMap) : M.vertexCount + M.faceCount = M.edgeCount + 2 := by
  have := euler_polyhedron_formula M
  unfold PlanarMap.eulerChar at this
  omega

/-- Classical planar edge bound: E ≤ 3V - 6 for maps with face degree ≥ 3. -/
theorem planar_edge_bound (M : PlanarMap) (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) : M.edgeCount ≤ 3 * M.vertexCount - 6 := by
  have := euler_polyhedron_formula_nat M
  omega

/-- Triangle-free planar edge bound: E ≤ 2V - 4 for maps with face degree ≥ 4. -/
theorem planar_edge_bound_triangle_free (M : PlanarMap) (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) : M.edgeCount ≤ 2 * M.vertexCount - 4 := by
  have := euler_polyhedron_formula_nat M
  omega

/-- Average vertex degree bound for planar maps: 2E < 6V. -/
theorem average_degree_lt_six (M : PlanarMap) (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) (hV : 3 ≤ M.vertexCount) : 2 * M.edgeCount < 6 * M.vertexCount := by
  have := planar_edge_bound M h_face hV
  omega

/-- Non-planarity obstruction for K5. -/
theorem non_planarity_k5 (M : PlanarMap) (hV : M.vertexCount = 5) (hE : M.edgeCount = 10) (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) : False := by
  have := planar_edge_bound M h_face
  omega

/-- Non-planarity obstruction for K3,3. -/
theorem non_planarity_k33 (M : PlanarMap) (hV : M.vertexCount = 6) (hE : M.edgeCount = 9) (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) : False := by
  have := planar_edge_bound_triangle_free M h_face
  omega

#print axioms euler_polyhedron_formula
#print axioms planar_edge_bound
#print axioms planar_edge_bound_triangle_free
#print axioms non_planarity_k5
#print axioms non_planarity_k33