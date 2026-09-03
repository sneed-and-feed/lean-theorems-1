import Mathlib.Data.Set.Basic

namespace DesarguesProjective

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

/-- A nondegenerate axial perspectivity. Besides the three corresponding side
    intersections lying on `L`, the axis is required not to be a side of either
    triangle. These six exclusions are dual to requiring the center of a
    central perspectivity not to be one of its six vertices. -/
def ProperAxialPerspective (PPlane : ProjectivePlane) (T₁ T₂ : Triangle PPlane)
    (L : PPlane.Line)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂) : Prop :=
  AxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂
      h_diff_AB h_diff_BC h_diff_CA ∧
    L ≠ lineThrough PPlane hAB₁ ∧
    L ≠ lineThrough PPlane hBC₁ ∧
    L ≠ lineThrough PPlane hCA₁ ∧
    L ≠ lineThrough PPlane hAB₂ ∧
    L ≠ lineThrough PPlane hBC₂ ∧
    L ≠ lineThrough PPlane hCA₂

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

/-- **Strengthened forward Desargues theorem:** the axis supplied for centrally
    perspective triangles is automatically a proper axis. -/
theorem desargues_projective_plane_proper (PPlane : ProjectivePlane)
    (h_des : IsDesarguesian PPlane) (T₁ T₂ : Triangle PPlane) (O : PPlane.Point)
    (h_central : CentralPerspective PPlane T₁ T₂ O)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂) :
    ∃ L : PPlane.Line,
      ProperAxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂
        h_diff_AB h_diff_BC h_diff_CA := sorry

/-- **Converse Desargues theorem in projective geometry:**
In any Desarguesian projective plane, proper axial perspective and distinct corresponding vertices determine a central perspective. -/
theorem desargues_converse_projective_plane (PPlane : ProjectivePlane)
    (h_des : IsDesarguesian PPlane) (T₁ T₂ : Triangle PPlane) (L : PPlane.Line)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂)
    (hAA : T₁.A ≠ T₂.A) (hBB : T₁.B ≠ T₂.B) (hCC : T₁.C ≠ T₂.C)
    (h_proper : ProperAxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂
      hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA) :
    ∃ O : PPlane.Point, CentralPerspective PPlane T₁ T₂ O := sorry

/-- In a Desarguesian plane, the nondegenerate forward and converse forms combine
    into an exact equivalence between central perspective and proper axial perspective. -/
theorem exists_centralPerspective_iff_exists_properAxialPerspective
    (PPlane : ProjectivePlane) (h_des : IsDesarguesian PPlane)
    (T₁ T₂ : Triangle PPlane)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂) :
    (∃ O : PPlane.Point, CentralPerspective PPlane T₁ T₂ O) ↔
      T₁.A ≠ T₂.A ∧ T₁.B ≠ T₂.B ∧ T₁.C ≠ T₂.C ∧
        ∃ L : PPlane.Line,
          ProperAxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂
            h_diff_AB h_diff_BC h_diff_CA := sorry

end DesarguesProjective
