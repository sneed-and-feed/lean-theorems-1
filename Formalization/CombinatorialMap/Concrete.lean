import Formalization.CombinatorialMap.Basic

open Equiv Perm

/-- The edge involution for the regular tetrahedron on 12 darts. -/
def tetrahedron_alpha : Perm (Fin 12) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7 * Equiv.swap 8 9 * Equiv.swap 10 11

/-- The vertex rotation permutation for the regular tetrahedron on 12 darts. -/
def tetrahedron_sigma : Perm (Fin 12) :=
  Equiv.swap 0 2 * Equiv.swap 2 4 *
  (Equiv.swap 1 8 * Equiv.swap 8 6) *
  (Equiv.swap 3 7 * Equiv.swap 7 10) *
  (Equiv.swap 5 11 * Equiv.swap 11 9)

/-- The combinatorial map of the regular tetrahedron. -/
def tetrahedronMap : CombinatorialMap (Fin 12) where
  α := tetrahedron_alpha
  σ := tetrahedron_sigma
  α_involution := by decide
  α_no_fixed_points := by decide

set_option maxRecDepth 200000 in
/-- The regular tetrahedron has 4 vertices. -/
theorem tetrahedron_vertexCount : tetrahedronMap.vertexCount = 4 := by decide

set_option maxRecDepth 200000 in
/-- The regular tetrahedron has 6 edges. -/
theorem tetrahedron_edgeCount : tetrahedronMap.edgeCount = 6 := by decide

set_option maxRecDepth 200000 in
/-- The regular tetrahedron has 4 triangular faces. -/
theorem tetrahedron_faceCount : tetrahedronMap.faceCount = 4 := by decide

set_option maxRecDepth 200000 in
/-- The regular tetrahedron satisfies Euler's formula χ = 4 - 6 + 4 = 2. -/
theorem tetrahedron_eulerChar : tetrahedronMap.eulerChar = 2 := by decide

-- Triangle Polygon Map on 6 darts (3 vertices, 3 edges, 2 faces)
def triangle_alpha : Perm (Fin 6) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

def triangle_sigma : Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 5 0

def triangleMap : CombinatorialMap (Fin 6) where
  α := triangle_alpha
  σ := triangle_sigma
  α_involution := by decide
  α_no_fixed_points := by decide

/-- The triangle polygon map satisfies Euler's formula χ = 3 - 3 + 2 = 2. -/
theorem triangle_eulerChar : triangleMap.eulerChar = 2 := by decide

-- Square Polygon Map on 8 darts (4 vertices, 4 edges, 2 faces)
def square_alpha : Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

def square_sigma : Perm (Fin 8) :=
  Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 5 6 * Equiv.swap 7 0

def squareMap : CombinatorialMap (Fin 8) where
  α := square_alpha
  σ := square_sigma
  α_involution := by decide
  α_no_fixed_points := by decide

/-- The square polygon map satisfies Euler's formula χ = 4 - 4 + 2 = 2. -/
theorem square_eulerChar : squareMap.eulerChar = 2 := by decide