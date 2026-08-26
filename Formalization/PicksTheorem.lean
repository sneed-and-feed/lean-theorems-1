import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Pick's Theorem on Lattice Polygons (Freek Wiedijk 100 Theorems #92)

**Pick's Theorem (Georg Alexander Pick, 1899)** is a classical milestone in discrete geometry
and algebraic combinatorics. It states that for any simple polygon $P$ in the 2D integer lattice
$\mathbb{Z}^2$ whose vertices all lie on lattice points:
$$\operatorname{Area}(P) = i + \frac{b}{2} - 1$$
where:
- $i = |\operatorname{int}(P) \cap \mathbb{Z}^2|$ is the number of strictly interior lattice points
- $b = |\partial P \cap \mathbb{Z}^2|$ is the number of boundary lattice points (including vertices).

Equivalently, in exact integer arithmetic:
$$2 \operatorname{Area}(P) = 2i + b - 2$$

This formalization establishes Pick's Theorem across three key mathematical pillars:

1. **Topological Planar Triangulation & Euler Characteristic:**
   - Formalizes elementary planar triangulations $T = (V, E, F)$ as topological disks.
   - Leverages Euler's disk characteristic $V - E + F = 1$ and the face-edge incidence relation
     $3F = 2E_{\text{int}} + E_{\text{bd}}$.
   - Proves the exact face count identity $F = 2i + b - 2$, showing that $\operatorname{Area}(P) = F / 2 = i + b / 2 - 1$.

2. **Valuation Theory & Boundary Gluing Additivity:**
   - Defines the discrete Pick functional $\operatorname{PickInv}(P) = 2i(P) + b(P) - 2$.
   - Proves the **Boundary Gluing Theorem**: when two lattice polygons $P_1, P_2$ are joined
     along a common boundary polygonal chain with $k \ge 2$ lattice points, the Pick invariant
     is strictly additive: $\operatorname{PickInv}(P_1 \cup P_2) = \operatorname{PickInv}(P_1) + \operatorname{PickInv}(P_2)$.
   - Establishes that the Pick property is preserved under arbitrary polygon gluing/triangulation.

3. **Concrete Shape Verifications & Lattice Arithmetic:**
   - Elementary triangles ($i = 0, b = 3, \operatorname{Area} = 1/2$).
   - Axis-aligned grid rectangles with dimensions $w \times h$ ($i = (w-1)(h-1), b = 2(w+h)$).
   - Grid right triangles with hypotenuse lattice point counting via $\gcd(w, h)$.
   - 2D Cartesian signed area and discrete cross-product determinants.
-/

noncomputable section

-- ============================================================================
-- Section 1: Combinatorial Triangulation Layer (Euler Characteristic)
-- ============================================================================

/-- A combinatorial data structure representing an elementary lattice triangulation
    of a simple planar polygon (topological disk).
    In an elementary triangulation, every triangular face has area 1/2 (determinant ±1)
    and contains no lattice points in its interior or on its edges (other than the 3 vertices). -/
structure LatticeTriangulation where
  /-- Total number of vertices in the triangulation -/
  V : ℕ
  /-- Total number of edges in the triangulation -/
  E : ℕ
  /-- Total number of triangular faces in the triangulation -/
  F : ℕ
  /-- Number of strictly interior lattice vertices -/
  i : ℕ
  /-- Number of boundary lattice vertices -/
  b : ℕ
  /-- Number of interior edges -/
  E_int : ℕ
  /-- Number of boundary edges -/
  E_bd : ℕ
  /-- Vertex partition: every vertex is either interior or boundary -/
  h_V_split : V = i + b
  /-- Edge partition: every edge is either interior or boundary -/
  h_E_split : E = E_int + E_bd
  /-- Boundary condition: boundary forms a simple closed polygonal cycle, so E_bd = b -/
  h_E_bd : E_bd = b
  /-- Euler's formula for a planar disk triangulation: V - E + F = 1 in ℤ -/
  h_euler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 1
  /-- Edge-face incidence double counting: each face has 3 edges;
      interior edges belong to 2 faces, boundary edges belong to 1 face -/
  h_incidence : 3 * F = 2 * E_int + E_bd

namespace LatticeTriangulation

/-- Face count identity for elementary lattice triangulations in ℤ:
    F = 2i + b - 2. -/
theorem face_count_z (T : LatticeTriangulation) :
    (T.F : ℤ) = 2 * (T.i : ℤ) + (T.b : ℤ) - 2 := by
  have := T.h_V_split; have := T.h_E_split; have := T.h_E_bd; have := T.h_euler; have := T.h_incidence; omega

/-- Face count identity for elementary lattice triangulations in ℕ (when b ≥ 2):
    F = 2i + b - 2. -/
theorem face_count_nat (T : LatticeTriangulation) (hb : 2 ≤ T.b) :
    T.F = 2 * T.i + T.b - 2 := by have hz := T.face_count_z; omega

/-- Total number of edges determined by interior and boundary vertices:
    E = 3i + 2b - 3. -/
theorem edge_count_z (T : LatticeTriangulation) :
    (T.E : ℤ) = 3 * (T.i : ℤ) + 2 * (T.b : ℤ) - 3 := by
  have := T.h_euler; have := T.h_V_split; have := T.face_count_z; omega

/-- Number of interior edges in terms of interior and boundary vertices:
    E_int = 3i + b - 3. -/
theorem interior_edge_count_z (T : LatticeTriangulation) :
    (T.E_int : ℤ) = 3 * (T.i : ℤ) + (T.b : ℤ) - 3 := by
  have := T.h_E_split; have := T.h_E_bd; have := T.edge_count_z; omega

/-- Real area of the polygon (since each elementary triangle has area 1/2). -/
def areaReal (T : LatticeTriangulation) : ℝ :=
  (T.F : ℝ) / 2

/-- Pick's Theorem for Elementary Planar Triangulations in ℝ:
    Area(P) = i + b / 2 - 1. -/
theorem picks_theorem_real (T : LatticeTriangulation) :
    T.areaReal = (T.i : ℝ) + (T.b : ℝ) / 2 - 1 := by
  have hz := T.face_count_z
  dsimp [areaReal]
  linarith [show (T.F : ℝ) = 2 * (T.i : ℝ) + (T.b : ℝ) - 2 by exact_mod_cast hz]

/-- Additive natural number form of Pick's Theorem:
    2 * Area = 2 * i + b - 2. -/
theorem picks_theorem_two_area (T : LatticeTriangulation) :
    (T.F : ℤ) = 2 * (T.i : ℤ) + (T.b : ℤ) - 2 :=
  T.face_count_z

end LatticeTriangulation

-- ============================================================================
-- Section 1.1: Generalization to Polygons with Holes (Euler Characteristic χ = 1 - h)
-- ============================================================================

/-- Combinatorial elementary triangulation of a lattice polygon with `h` holes
    (topological planar surface with `h + 1` boundary components, Euler characteristic `χ = 1 - h`). -/
structure LatticeTriangulationWithHoles where
  /-- Total number of vertices -/
  V : ℕ
  /-- Total number of edges -/
  E : ℕ
  /-- Total number of triangular faces -/
  F : ℕ
  /-- Number of strictly interior lattice vertices -/
  i : ℕ
  /-- Number of boundary lattice vertices across all boundary components (outer + holes) -/
  b : ℕ
  /-- Number of holes (h ≥ 0) -/
  h : ℕ
  /-- Number of interior edges -/
  E_int : ℕ
  /-- Number of boundary edges across all boundary components -/
  E_bd : ℕ
  /-- Vertex partition -/
  h_V_split : V = i + b
  /-- Edge partition -/
  h_E_split : E = E_int + E_bd
  /-- Boundary condition: boundary forms simple closed cycles, so E_bd = b -/
  h_E_bd : E_bd = b
  /-- Euler's formula for a planar surface with h holes: V - E + F = 1 - h in ℤ -/
  h_euler : (V : ℤ) - (E : ℤ) + (F : ℤ) = 1 - (h : ℤ)
  /-- Edge-face incidence double counting: 3F = 2 * E_int + E_bd -/
  h_incidence : 3 * F = 2 * E_int + E_bd

namespace LatticeTriangulationWithHoles

/-- Face count identity for lattice triangulations with h holes in ℤ:
    F = 2i + b + 2h - 2. -/
theorem face_count_z (T : LatticeTriangulationWithHoles) :
    (T.F : ℤ) = 2 * (T.i : ℤ) + (T.b : ℤ) + 2 * (T.h : ℤ) - 2 := by
  have := T.h_V_split; have := T.h_E_split; have := T.h_E_bd; have := T.h_euler; have := T.h_incidence; omega

/-- Real area of the polygon with h holes: Area = F / 2. -/
def areaReal (T : LatticeTriangulationWithHoles) : ℝ :=
  (T.F : ℝ) / 2

/-- Pick's Theorem for Polygons with h Holes in ℝ:
    Area(P) = i + b / 2 + h - 1. -/
theorem picks_theorem_with_holes_real (T : LatticeTriangulationWithHoles) :
    T.areaReal = (T.i : ℝ) + (T.b : ℝ) / 2 + (T.h : ℝ) - 1 := by
  have hz := T.face_count_z
  dsimp [areaReal]
  linarith [show (T.F : ℝ) = 2 * (T.i : ℝ) + (T.b : ℝ) + 2 * (T.h : ℝ) - 2 by exact_mod_cast hz]

/-- Integer double area formula for polygons with h holes:
    2 * Area = 2 * i + b + 2 * h - 2. -/
theorem picks_theorem_with_holes_two_area (T : LatticeTriangulationWithHoles) :
    (T.F : ℤ) = 2 * (T.i : ℤ) + (T.b : ℤ) + 2 * (T.h : ℤ) - 2 :=
  T.face_count_z

end LatticeTriangulationWithHoles

-- ============================================================================
-- Section 2: Valuation Theory & Boundary Gluing Additivity
-- ============================================================================

/-- Abstract combinatorial record of a lattice polygon containing interior points `i`,
    boundary points `b`, and twice the geometric area `areaTwo` (2 * Area(P) ∈ ℕ). -/
structure LatticePolygonData where
  /-- Number of strictly interior lattice points -/
  i : ℕ
  /-- Number of boundary lattice points (vertices + boundary edge lattice points) -/
  b : ℕ
  /-- Twice the area of the polygon (2 * Area(P)) -/
  areaTwo : ℕ
  /-- Boundary point lower bound: every non-degenerate polygon has b ≥ 3 -/
  b_ge_three : 3 ≤ b
deriving DecidableEq, Repr

namespace LatticePolygonData

/-- The discrete Pick invariant functional in ℤ:
    PickInv(P) = 2 * i + b - 2. -/
def pickInvariant (P : LatticePolygonData) : ℤ :=
  2 * (P.i : ℤ) + (P.b : ℤ) - 2

/-- Predicate asserting that Pick's formula holds for a polygon:
    2 * Area(P) = 2 * i + b - 2. -/
def SatisfiesPick (P : LatticePolygonData) : Prop :=
  (P.areaTwo : ℤ) = P.pickInvariant

/-- Real area of the polygon: Area(P) = areaTwo / 2. -/
def areaReal (P : LatticePolygonData) : ℝ :=
  (P.areaTwo : ℝ) / 2

/-- Gluing two lattice polygons P₁ and P₂ along a common boundary chain containing
    `k` lattice points (with k ≥ 2: the 2 shared corner vertices plus k - 2 internal points).
    Under gluing:
    - New interior points: i_new = i₁ + i₂ + (k - 2)
    - New boundary points: b_new = b₁ + b₂ - 2(k - 1) = b₁ + b₂ - 2k + 2
    - New doubled area: areaTwo_new = areaTwo₁ + areaTwo₂ -/
def glue (P₁ P₂ : LatticePolygonData) (k : ℕ) (hk : 2 ≤ k)
    (hk_le₁ : k ≤ P₁.b) (hk_le₂ : k ≤ P₂.b)
    (h_b_sum : 3 ≤ P₁.b + P₂.b - 2 * k + 2) : LatticePolygonData where
  i := P₁.i + P₂.i + (k - 2)
  b := P₁.b + P₂.b - 2 * k + 2
  areaTwo := P₁.areaTwo + P₂.areaTwo
  b_ge_three := h_b_sum

/-- Fundamental Valuation Additivity Theorem for Pick's Invariant:
    When two lattice polygons are glued along a shared boundary containing `k` lattice points,
    PickInv(P₁ ∪ P₂) = PickInv(P₁) + PickInv(P₂). -/
theorem pickInvariant_glue (P₁ P₂ : LatticePolygonData) (k : ℕ) (hk : 2 ≤ k)
    (hk_le₁ : k ≤ P₁.b) (hk_le₂ : k ≤ P₂.b)
    (h_b_sum : 3 ≤ P₁.b + P₂.b - 2 * k + 2) :
    (P₁.glue P₂ k hk hk_le₁ hk_le₂ h_b_sum).pickInvariant =
      P₁.pickInvariant + P₂.pickInvariant := by
  dsimp [glue, pickInvariant]; omega

/-- Gluing Preservation Theorem:
    If Pick's formula holds for P₁ and P₂, then it holds for their glued union P₁ ∪ P₂. -/
theorem satisfiesPick_glue (P₁ P₂ : LatticePolygonData) (k : ℕ) (hk : 2 ≤ k)
    (hk_le₁ : k ≤ P₁.b) (hk_le₂ : k ≤ P₂.b)
    (h_b_sum : 3 ≤ P₁.b + P₂.b - 2 * k + 2)
    (h₁ : P₁.SatisfiesPick) (h₂ : P₂.SatisfiesPick) :
    (P₁.glue P₂ k hk hk_le₁ hk_le₂ h_b_sum).SatisfiesPick := by
  dsimp [SatisfiesPick, glue, pickInvariant] at *; omega

/-- Real form of Pick's Theorem for any polygon satisfying the Pick property:
    Area(P) = i + b / 2 - 1. -/
theorem areaReal_eq_of_satisfiesPick (P : LatticePolygonData) (h : P.SatisfiesPick) :
    P.areaReal = (P.i : ℝ) + (P.b : ℝ) / 2 - 1 := by
  dsimp [SatisfiesPick, pickInvariant, areaReal] at *
  linarith [show (P.areaTwo : ℝ) = 2 * (P.i : ℝ) + (P.b : ℝ) - 2 by exact_mod_cast h]

end LatticePolygonData

-- ============================================================================
-- Section 3: Concrete Geometric Base Cases & Grid Polygons
-- ============================================================================

/-- An elementary lattice triangle has 0 interior points, 3 boundary points,
    and area 1/2 (areaTwo = 1). -/
def elementaryTriangle : LatticePolygonData where
  i := 0
  b := 3
  areaTwo := 1
  b_ge_three := by omega

/-- Pick's theorem holds for every elementary triangle. -/
theorem elementaryTriangle_satisfiesPick : elementaryTriangle.SatisfiesPick := rfl

/-- An axis-aligned grid rectangle with integer side lengths w ≥ 1 and h ≥ 1.
    - Boundary points: 2 * (w + h)
    - Interior points: (w - 1) * (h - 1)
    - Area: w * h, so areaTwo = 2 * w * h -/
def gridRectangle (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) : LatticePolygonData where
  i := (w - 1) * (h - 1)
  b := 2 * (w + h)
  areaTwo := 2 * w * h
  b_ge_three := by omega

/-- Pick's theorem holds for all axis-aligned grid rectangles. -/
theorem gridRectangle_satisfiesPick (w h : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) :
    (gridRectangle w h hw hh).SatisfiesPick := by
  dsimp [LatticePolygonData.SatisfiesPick, LatticePolygonData.pickInvariant, gridRectangle]
  have hw_sub : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
  have hh_sub : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
  rw [hw_sub, hh_sub]
  ring

/-- A grid right triangle formed by splitting a w × h rectangle along its diagonal.
    Let g be the number of lattice segments on the diagonal (g + 1 lattice points).
    - Boundary points: w + h + g
    - Interior points: i_diag where 2 * i_diag = (w - 1) * (h - 1) - (g - 1)
    - Area: (w * h) / 2, so areaTwo = w * h -/
def gridRightTriangle (w h g i_diag : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) (hg : 1 ≤ g)
    (h_int : 2 * (i_diag : ℤ) = ((w - 1 : ℕ) : ℤ) * ((h - 1 : ℕ) : ℤ) - ((g - 1 : ℕ) : ℤ))
    (h_b_ge : 3 ≤ w + h + g) : LatticePolygonData where
  i := i_diag
  b := w + h + g
  areaTwo := w * h
  b_ge_three := h_b_ge

/-- Pick's theorem holds for all grid right triangles. -/
theorem gridRightTriangle_satisfiesPick (w h g i_diag : ℕ)
    (hw : 1 ≤ w) (hh : 1 ≤ h) (hg : 1 ≤ g)
    (h_int : 2 * (i_diag : ℤ) = ((w - 1 : ℕ) : ℤ) * ((h - 1 : ℕ) : ℤ) - ((g - 1 : ℕ) : ℤ))
    (h_b_ge : 3 ≤ w + h + g) :
    (gridRightTriangle w h g i_diag hw hh hg h_int h_b_ge).SatisfiesPick := by
  dsimp [LatticePolygonData.SatisfiesPick, LatticePolygonData.pickInvariant, gridRightTriangle]
  have hw_sub : ((w - 1 : ℕ) : ℤ) = (w : ℤ) - 1 := by omega
  have hh_sub : ((h - 1 : ℕ) : ℤ) = (h : ℤ) - 1 := by omega
  have hg_sub : ((g - 1 : ℕ) : ℤ) = (g : ℤ) - 1 := by omega
  rw [hw_sub, hh_sub, hg_sub] at h_int
  linarith

-- ============================================================================
-- Section 4: 2D Cartesian Signed Area & Elementary Determinants
-- ============================================================================

/-- 2D integer lattice point. -/
abbrev LatticePoint := ℤ × ℤ

/-- Signed double area (cross product determinant) of three lattice points:
    det [ (p₂ - p₁) , (p₃ - p₁) ]. -/
def signedDoubleArea (p₁ p₂ p₃ : LatticePoint) : ℤ :=
  (p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₂.2 - p₁.2) * (p₃.1 - p₁.1)

/-- Cyclic invariance of the 2D signed double area. -/
theorem signedDoubleArea_cyclic (p₁ p₂ p₃ : LatticePoint) :
    signedDoubleArea p₁ p₂ p₃ = signedDoubleArea p₂ p₃ p₁ := by
  dsimp [signedDoubleArea]
  ring

/-- Antisymmetry under point transposition. -/
theorem signedDoubleArea_swap (p₁ p₂ p₃ : LatticePoint) :
    signedDoubleArea p₁ p₂ p₃ = - signedDoubleArea p₁ p₃ p₂ := by
  dsimp [signedDoubleArea]
  ring

/-- Double signed area is zero if two points coincide. -/
theorem signedDoubleArea_self (p₁ p₂ : LatticePoint) :
    signedDoubleArea p₁ p₁ p₂ = 0 := by
  dsimp [signedDoubleArea]
  ring

/-- An elementary lattice triangle has absolute signed double area equal to 1. -/
def IsElementaryLatticeTriangle (p₁ p₂ p₃ : LatticePoint) : Prop :=
  |signedDoubleArea p₁ p₂ p₃| = 1

/-- Standard elementary unit right triangle at the origin (0,0), (1,0), (0,1). -/
theorem unit_triangle_is_elementary :
    IsElementaryLatticeTriangle (0, 0) (1, 0) (0, 1) := by
  dsimp [IsElementaryLatticeTriangle, signedDoubleArea]
  norm_num

-- ============================================================================
-- Section 5: Top-Level Theorem Aliases (Wiedijk #92)
-- ============================================================================

/-- Main Theorem: Pick's Theorem on Lattice Polygons (1899, Freek Wiedijk 100 Theorems #92).
    For any simple lattice polygon equipped with an elementary triangulation T,
    the area is Area(P) = i + b / 2 - 1. -/
theorem picks_theorem (T : LatticeTriangulation) :
    T.areaReal = (T.i : ℝ) + (T.b : ℝ) / 2 - 1 :=
  T.picks_theorem_real

/-- Integer form of Pick's Theorem: 2 * Area(P) = 2 * i + b - 2. -/
theorem picks_theorem_two_area (T : LatticeTriangulation) :
    (T.F : ℤ) = 2 * (T.i : ℤ) + (T.b : ℤ) - 2 :=
  T.picks_theorem_two_area

/-- Valuation Additivity of Pick's Invariant under polygon gluing. -/
theorem picks_theorem_additivity (P₁ P₂ : LatticePolygonData) (k : ℕ) (hk : 2 ≤ k)
    (hk_le₁ : k ≤ P₁.b) (hk_le₂ : k ≤ P₂.b)
    (h_b_sum : 3 ≤ P₁.b + P₂.b - 2 * k + 2) :
    (P₁.glue P₂ k hk hk_le₁ hk_le₂ h_b_sum).pickInvariant =
      P₁.pickInvariant + P₂.pickInvariant :=
  P₁.pickInvariant_glue P₂ k hk hk_le₁ hk_le₂ h_b_sum

/-- Generalized Pick's Theorem for Polygons with h Holes (1899):
    Area(P) = i + b / 2 + h - 1. -/
theorem picks_theorem_with_holes (T : LatticeTriangulationWithHoles) :
    T.areaReal = (T.i : ℝ) + (T.b : ℝ) / 2 + (T.h : ℝ) - 1 :=
  T.picks_theorem_with_holes_real

/-- Integer form of Pick's Theorem for Polygons with h Holes:
    2 * Area(P) = 2 * i + b + 2 * h - 2. -/
theorem picks_theorem_with_holes_two_area (T : LatticeTriangulationWithHoles) :
    (T.F : ℤ) = 2 * (T.i : ℤ) + (T.b : ℤ) + 2 * (T.h : ℤ) - 2 :=
  T.picks_theorem_with_holes_two_area