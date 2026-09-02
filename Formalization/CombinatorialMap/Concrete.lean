import Formalization.CombinatorialMap.Basic

open Equiv Perm

/-!
# Concrete Polyhedral Maps and Toroidal Certificates

This module defines concrete machine-checked combinatorial maps:
1. Platonic Solids & Planar Polygons:
   - `tetrahedronMap`: Regular tetrahedron on 12 darts (V = 4, E = 6, F = 4, χ = 2).
   - `cubeMap`: Regular cube on 24 darts (V = 8, E = 12, F = 6, χ = 2).
   - `triangleMap`: Triangular face map on 6 darts (V = 3, E = 3, F = 2, χ = 2).
   - `squareMap`: Quadrilateral face map on 8 darts (V = 4, E = 4, F = 2, χ = 2).
2. Sharpness & Tightness Certificate (AP-11, AP-30):
   - `k5_torusMap`: Concrete toroidal embedding of K₅ on 20 darts with
     V = 5, E = 10, F = 5, χ = 0, genus = 1.
-/

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

-- Regular Cube on 24 darts (8 vertices, 12 edges, 6 quadrilateral faces)
def cube_alpha : Perm (Fin 24) :=
  Equiv.swap 0 5 * Equiv.swap 3 8 * Equiv.swap 6 11 * Equiv.swap 2 9 *
  Equiv.swap 13 17 * Equiv.swap 16 20 * Equiv.swap 19 23 * Equiv.swap 14 22 *
  Equiv.swap 1 12 * Equiv.swap 4 15 * Equiv.swap 7 18 * Equiv.swap 10 21

def cube_sigma : Perm (Fin 24) :=
  (Equiv.swap 0 1 * Equiv.swap 1 2) *
  (Equiv.swap 3 4 * Equiv.swap 4 5) *
  (Equiv.swap 6 7 * Equiv.swap 7 8) *
  (Equiv.swap 9 10 * Equiv.swap 10 11) *
  (Equiv.swap 12 13 * Equiv.swap 13 14) *
  (Equiv.swap 15 16 * Equiv.swap 16 17) *
  (Equiv.swap 18 19 * Equiv.swap 19 20) *
  (Equiv.swap 21 22 * Equiv.swap 22 23)

set_option maxRecDepth 500000 in
def cubeMap : CombinatorialMap (Fin 24) where
  α := cube_alpha
  σ := cube_sigma
  α_involution := by ext x; revert x; decide
  α_no_fixed_points := by decide

set_option maxRecDepth 200000 in
/-- The regular cube satisfies Euler's formula χ = 8 - 12 + 6 = 2. -/
theorem cube_eulerChar : cubeMap.eulerChar = 2 := by decide

/-! ### Toroidal Embedding of K₅ (Sharpness & Tightness Certificate) -/

/-- Edge involution for K₅ on the torus (10 edges swapping 20 darts). -/
def k5_torus_alpha : Perm (Fin 20) :=
  Equiv.swap 0 4 * Equiv.swap 1 8 * Equiv.swap 2 12 * Equiv.swap 3 16 *
  Equiv.swap 5 9 * Equiv.swap 6 13 * Equiv.swap 7 17 *
  Equiv.swap 10 14 * Equiv.swap 11 18 *
  Equiv.swap 15 19

/-- Vertex rotation for K₅ on the torus (5 vertices of degree 4, each a 4-cycle). -/
def k5_torus_sigma : Perm (Fin 20) :=
  (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3) *
  (Equiv.swap 4 5 * Equiv.swap 5 7 * Equiv.swap 7 6) *
  (Equiv.swap 8 10 * Equiv.swap 10 9 * Equiv.swap 9 11) *
  (Equiv.swap 12 15 * Equiv.swap 15 14 * Equiv.swap 14 13) *
  (Equiv.swap 16 17 * Equiv.swap 17 19 * Equiv.swap 19 18)

/-- The toroidal combinatorial map of K₅ on 20 darts. -/
def k5_torusMap : CombinatorialMap (Fin 20) where
  α := k5_torus_alpha
  σ := k5_torus_sigma
  α_involution := by ext x; revert x; decide
  α_no_fixed_points := by decide

set_option maxRecDepth 200000 in
/-- K₅ on the torus has 5 vertices. -/
theorem k5_torus_vertexCount : k5_torusMap.vertexCount = 5 := by decide

set_option maxRecDepth 200000 in
/-- K₅ on the torus has 10 edges. -/
theorem k5_torus_edgeCount : k5_torusMap.edgeCount = 10 := by decide

set_option maxRecDepth 200000 in
/-- K₅ on the torus has 5 quadrilateral faces. -/
theorem k5_torus_faceCount : k5_torusMap.faceCount = 5 := by decide

set_option maxRecDepth 200000 in
/-- Tightness certificate: K₅ embeds on the torus with Euler characteristic χ = 0. -/
theorem k5_torus_eulerChar : k5_torusMap.eulerChar = 0 := by decide

set_option maxRecDepth 200000 in
/-- Tightness certificate: K₅ embeds on the torus with genus = 1. -/
theorem k5_torus_genus : k5_torusMap.genus = 1 := by decide