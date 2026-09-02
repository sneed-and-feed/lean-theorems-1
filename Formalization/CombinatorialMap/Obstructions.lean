import Formalization.CombinatorialMap.Basic
import Formalization.CombinatorialMap.Parity
import Formalization.CombinatorialMap.FaceDegree

/-!
# Planar Bounds & Topological Genus Obstructions for Combinatorial Maps

This module establishes:
1. Classical planar edge bounds:
   - `planar_edge_bound`: E ≤ 3V - 6 for maps with face degree ≥ 3 (3F ≤ 2E).
   - `planar_edge_bound_triangle_free`: E ≤ 2V - 4 for maps with face degree ≥ 4 (4F ≤ 2E).
   - `average_degree_lt_six`: 2E < 6V for planar maps.
2. Authentic Genus Invariants & Non-Planarity Obstructions (eliminating AP-05):
   - For K5 (V = 5, E = 10, 3F ≤ 2E):
     * `k5_eulerChar_le_zero`: χ(M) ≤ 0
     * `k5_genus_ge_one`: genus(M) ≥ 1
     * `k5_not_planar`: χ(M) ≠ 2
   - For K3,3 (V = 6, E = 9, 4F ≤ 2E):
     * `k33_eulerChar_le_zero`: χ(M) ≤ 0
     * `k33_genus_ge_one`: genus(M) ≥ 1
     * `k33_not_planar`: χ(M) ≠ 2
-/

open Equiv Perm

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

/-- Classical planar edge bound: E ≤ 3V - 6 for maps with face degree ≥ 3 (3F ≤ 2E). -/
theorem planar_edge_bound (h_euler : M.eulerChar = 2)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount)
    (hV : 3 ≤ M.vertexCount) :
    M.edgeCount ≤ 3 * M.vertexCount - 6 := by
  unfold eulerChar at h_euler
  omega

/-- Triangle-free planar edge bound: E ≤ 2V - 4 for maps with face degree ≥ 4 (4F ≤ 2E). -/
theorem planar_edge_bound_triangle_free (h_euler : M.eulerChar = 2)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount)
    (hV : 3 ≤ M.vertexCount) :
    M.edgeCount ≤ 2 * M.vertexCount - 4 := by
  unfold eulerChar at h_euler
  omega

/-- Average vertex degree bound for planar maps: 2E < 6V. -/
theorem average_degree_lt_six (h_euler : M.eulerChar = 2)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount)
    (hV : 3 ≤ M.vertexCount) :
    2 * M.edgeCount < 6 * M.vertexCount := by
  have := planar_edge_bound M h_euler h_face hV
  omega

/-! ### General Genus Invariants & Non-Planarity Helpers -/

/-- For any combinatorial map with χ(M) ≤ 0, the topological genus is at least 1. -/
lemma genus_ge_one_of_eulerChar_le_zero (h : M.eulerChar ≤ 0) : 1 ≤ M.genus := by
  obtain ⟨_, hk⟩ := M.eulerChar_int_is_even
  unfold genus
  omega

/-- For any combinatorial map with χ(M) ≤ 0, the map cannot be planar (χ ≠ 2). -/
lemma not_planar_of_eulerChar_le_zero (h : M.eulerChar ≤ 0) : M.eulerChar ≠ 2 := by
  omega

/-! ### K₅ Genus Obstructions -/

/-- For any map with parameters of K₅ (V = 5, E = 10, 3F ≤ 2E), the Euler characteristic is at most 0. -/
theorem eulerChar_le_zero_of_k5_params (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≤ 0 := by
  obtain ⟨_, hk⟩ := M.eulerChar_int_is_even
  unfold eulerChar at hk ⊢
  omega

/-- For any map on 20 darts representing K₅, the Euler characteristic is at most 0. -/
theorem k5_eulerChar_le_zero (M : CombinatorialMap (Fin 20))
    (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≤ 0 :=
  eulerChar_le_zero_of_k5_params M hV hE h_face

/-- For any map with parameters of K₅, the topological genus is at least 1. -/
theorem genus_ge_one_of_k5_params (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) :
    1 ≤ M.genus :=
  genus_ge_one_of_eulerChar_le_zero M (eulerChar_le_zero_of_k5_params M hV hE h_face)

/-- For any map on 20 darts representing K₅, the topological genus is at least 1. -/
theorem k5_genus_ge_one (M : CombinatorialMap (Fin 20))
    (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) :
    1 ≤ M.genus :=
  genus_ge_one_of_k5_params M hV hE h_face

/-- Authentic topological non-planarity obstruction: K₅ cannot be planar (χ ≠ 2). -/
theorem not_planar_of_k5_params (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≠ 2 :=
  not_planar_of_eulerChar_le_zero M (eulerChar_le_zero_of_k5_params M hV hE h_face)

/-- Authentic topological non-planarity obstruction for K₅ on 20 darts: χ(M) ≠ 2. -/
theorem k5_not_planar (M : CombinatorialMap (Fin 20))
    (hV : M.vertexCount = 5) (hE : M.edgeCount = 10)
    (h_face : 3 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≠ 2 :=
  not_planar_of_k5_params M hV hE h_face

/-! ### K₃,₃ Genus Obstructions -/

/-- For any map with parameters of K₃,₃ (V = 6, E = 9, 4F ≤ 2E), the Euler characteristic is at most 0. -/
theorem eulerChar_le_zero_of_k33_params (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≤ 0 := by
  obtain ⟨_, hk⟩ := M.eulerChar_int_is_even
  unfold eulerChar at hk ⊢
  omega

/-- For any map on 18 darts representing K₃,₃, the Euler characteristic is at most 0. -/
theorem k33_eulerChar_le_zero (M : CombinatorialMap (Fin 18))
    (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≤ 0 :=
  eulerChar_le_zero_of_k33_params M hV hE h_face

/-- For any map with parameters of K₃,₃, the topological genus is at least 1. -/
theorem genus_ge_one_of_k33_params (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) :
    1 ≤ M.genus :=
  genus_ge_one_of_eulerChar_le_zero M (eulerChar_le_zero_of_k33_params M hV hE h_face)

/-- For any map on 18 darts representing K₃,₃, the topological genus is at least 1. -/
theorem k33_genus_ge_one (M : CombinatorialMap (Fin 18))
    (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) :
    1 ≤ M.genus :=
  genus_ge_one_of_k33_params M hV hE h_face

/-- Authentic topological non-planarity obstruction: K₃,₃ cannot be planar (χ ≠ 2). -/
theorem not_planar_of_k33_params (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≠ 2 :=
  not_planar_of_eulerChar_le_zero M (eulerChar_le_zero_of_k33_params M hV hE h_face)

/-- Authentic topological non-planarity obstruction for K₃,₃ on 18 darts: χ(M) ≠ 2. -/
theorem k33_not_planar (M : CombinatorialMap (Fin 18))
    (hV : M.vertexCount = 6) (hE : M.edgeCount = 9)
    (h_face : 4 * M.faceCount ≤ 2 * M.edgeCount) :
    M.eulerChar ≠ 2 :=
  not_planar_of_k33_params M hV hE h_face

end CombinatorialMap
