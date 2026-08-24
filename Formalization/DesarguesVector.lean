import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Module

/-!
# Desargues's Theorem in Vector and Axiomatic Projective Geometry (1639)

This module formalizes **Desargues's Theorem** (Girard Desargues, 1639; David Hilbert, 1899)
across both its **coordinate/vector** formulation and its **axiomatic projective plane** formulation (Wiedijk #53).

## Geometric Background
In the classical nondegenerate Desargues theorem and its converse, two triangles are in
**central perspective** (lines through corresponding vertices concur at a point $O$)
if and only if they are in **axial perspective** (intersections of corresponding pairs of
sides are collinear on a line $L$).  The definitions below make the degeneracy conditions explicit.

1. **Vector Formulation (Theorem 1):** Over any module $V$ over a commutative ring $K$, the side-intersection
   vectors $P, Q, R$ satisfy the linear dependence relation $\nu P + \lambda Q + \mu R = 0$.
2. **Axiomatic Projective Planes:** `IsDesarguesian` records the forward implication from
   central perspective to axial perspective.  The converse needs additional nondegeneracy
   hypotheses absent from the original `AxialPerspective` definition; a four-point
   counterexample below makes that boundary explicit.

## References
* G. Desargues (1639), *Brouillon project d'une atteinte aux événemens des rencontres du Cône avec un Plan*.
* D. Hilbert (1899), *Grundlagen der Geometrie*, Teubner.
* H. S. M. Coxeter (1987), *Projective Geometry*, Springer-Verlag.
* Freek Wiedijk, *Formalizing 100 Theorems*, #53.
-/

-- ============================================================================
-- Section 1: Vector Formulation of Desargues's Theorem
-- ============================================================================

/-- Desargues's Theorem (Vector Formulation):
    Two triangles in central perspective from O have their side-intersection points
    P, Q, R satisfying a linear dependence relation ν • P + λ • Q + μ • R = 0 (axial perspective / collinearity). -/
theorem desargues_vector {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (O A₁ B₁ C₁ A₂ B₂ C₂ : V)
    (a b c «λ» μ ν : K)
    (hA₂ : A₂ = a • A₁ + «λ» • O)
    (hB₂ : B₂ = b • B₁ + μ • O)
    (hC₂ : C₂ = c • C₁ + ν • O)
    (P Q R : V)
    (hP : P = μ • A₂ - «λ» • B₂)
    (hQ : Q = ν • B₂ - μ • C₂)
    (hR : R = «λ» • C₂ - ν • A₂) :
    ν • P + «λ» • Q + μ • R = 0 ∧
    P = (μ * a) • A₁ - («λ» * b) • B₁ ∧
    Q = (ν * b) • B₁ - (μ * c) • C₁ ∧
    R = («λ» * c) • C₁ - (ν * a) • A₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP, hQ, hR]
    simp only [smul_sub, ← mul_smul]
    rw [mul_comm ν μ, mul_comm «λ» ν, mul_comm μ «λ»]
    abel
  · rw [hP, hA₂, hB₂]
    simp only [smul_add, ← mul_smul]
    rw [mul_comm μ «λ»]
    abel
  · rw [hQ, hB₂, hC₂]
    simp only [smul_add, ← mul_smul]
    rw [mul_comm ν μ]
    abel
  · rw [hR, hC₂, hA₂]
    simp only [smul_add, ← mul_smul]
    rw [mul_comm «λ» ν]
    abel

-- ============================================================================
-- Section 2: Axiomatic Projective Planes
-- ============================================================================

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

private lemma inc_lineThrough_left (PPlane : ProjectivePlane)
    {p q : PPlane.Point} (hpq : p ≠ q) :
    PPlane.Inc p (lineThrough PPlane hpq) :=
  (PPlane.line_through p q hpq).choose_spec.1.1

private lemma inc_lineThrough_right (PPlane : ProjectivePlane)
    {p q : PPlane.Point} (hpq : p ≠ q) :
    PPlane.Inc q (lineThrough PPlane hpq) :=
  (PPlane.line_through p q hpq).choose_spec.1.2

private lemma meetLines_eq_of_inc (PPlane : ProjectivePlane)
    {l₁ l₂ : PPlane.Line} (hl : l₁ ≠ l₂) (p : PPlane.Point)
    (hp₁ : PPlane.Inc p l₁) (hp₂ : PPlane.Inc p l₂) :
    meetLines PPlane hl = p := by
  apply (PPlane.point_intersection l₁ l₂ hl).unique
  · exact (PPlane.point_intersection l₁ l₂ hl).choose_spec.1
  · exact ⟨hp₁, hp₂⟩

-- ============================================================================
-- Section 3: Projective Triangles and Perspectives
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
-- Section 4: Desarguesian Planes & the Degenerate Converse Boundary
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

/-- **Forward Desargues axiom in projective geometry (1639 / Hilbert 1899):**
    In a plane satisfying `IsDesarguesian`, central perspective implies axial perspective. -/
theorem desargues_projective_plane (PPlane : ProjectivePlane) (h_des : IsDesarguesian PPlane)
    (T₁ T₂ : Triangle PPlane) (O : PPlane.Point)
    (h_central : CentralPerspective PPlane T₁ T₂ O)
    (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
    (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
    (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
    (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
    (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
    (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂) :
    ∃ L : PPlane.Line, AxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA :=
  h_des T₁ T₂ O h_central hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂ h_diff_AB h_diff_BC h_diff_CA

/-- `AxialPerspective` as defined above does **not** imply central perspective.

Take four points with no three collinear.  The triangles `(p₁,p₂,p₃)` and
`(p₁,p₃,p₄)` share their first corresponding vertex.  Their three corresponding
side intersections are `p₁`, `p₃`, and `p₁`, hence are axial on the line
`p₁p₃`; but `CentralPerspective` explicitly requires the corresponding first
vertices to be distinct.  Thus a dual Desargues theorem requires at least the
three corresponding-vertex inequalities (and a genuine duality argument). -/
theorem axialPerspective_not_implies_central (PPlane : ProjectivePlane) :
    ∃ (T₁ T₂ : Triangle PPlane)
      (hAB₁ : T₁.A ≠ T₁.B) (hAB₂ : T₂.A ≠ T₂.B)
      (hBC₁ : T₁.B ≠ T₁.C) (hBC₂ : T₂.B ≠ T₂.C)
      (hCA₁ : T₁.C ≠ T₁.A) (hCA₂ : T₂.C ≠ T₂.A)
      (h_diff_AB : lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂)
      (h_diff_BC : lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂)
      (h_diff_CA : lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂)
      (L : PPlane.Line),
      AxialPerspective PPlane T₁ T₂ L hAB₁ hAB₂ hBC₁ hBC₂ hCA₁ hCA₂
          h_diff_AB h_diff_BC h_diff_CA ∧
        ¬ ∃ O : PPlane.Point, CentralPerspective PPlane T₁ T₂ O := by
  rcases PPlane.four_points with
    ⟨p₁, p₂, p₃, p₄, hp₁₂, hp₁₃, hp₁₄, hp₂₃, _hp₂₄, hp₃₄,
      hnc₁₂₃, _hnc₁₂₄, hnc₁₃₄, hnc₂₃₄⟩
  let T₁ : Triangle PPlane :=
    { A := p₁
      B := p₂
      C := p₃
      h_non_collinear := by
        rintro ⟨l, hl⟩
        exact hnc₁₂₃ l hl }
  let T₂ : Triangle PPlane :=
    { A := p₁
      B := p₃
      C := p₄
      h_non_collinear := by
        rintro ⟨l, hl⟩
        exact hnc₁₃₄ l hl }
  have hAB₁ : T₁.A ≠ T₁.B := by simpa [T₁] using hp₁₂
  have hAB₂ : T₂.A ≠ T₂.B := by simpa [T₂] using hp₁₃
  have hBC₁ : T₁.B ≠ T₁.C := by simpa [T₁] using hp₂₃
  have hBC₂ : T₂.B ≠ T₂.C := by simpa [T₂] using hp₃₄
  have hCA₁ : T₁.C ≠ T₁.A := by simpa [T₁] using hp₁₃.symm
  have hCA₂ : T₂.C ≠ T₂.A := by simpa [T₂] using hp₁₄.symm
  have h_diff_AB :
      lineThrough PPlane hAB₁ ≠ lineThrough PPlane hAB₂ := by
    intro hlines
    apply hnc₁₂₃ (lineThrough PPlane hAB₁)
    refine ⟨inc_lineThrough_left PPlane hAB₁,
      inc_lineThrough_right PPlane hAB₁, ?_⟩
    rw [hlines]
    exact inc_lineThrough_right PPlane hAB₂
  have h_diff_BC :
      lineThrough PPlane hBC₁ ≠ lineThrough PPlane hBC₂ := by
    intro hlines
    apply hnc₂₃₄ (lineThrough PPlane hBC₁)
    refine ⟨inc_lineThrough_left PPlane hBC₁,
      inc_lineThrough_right PPlane hBC₁, ?_⟩
    rw [hlines]
    exact inc_lineThrough_right PPlane hBC₂
  have h_diff_CA :
      lineThrough PPlane hCA₁ ≠ lineThrough PPlane hCA₂ := by
    intro hlines
    apply hnc₁₃₄ (lineThrough PPlane hCA₁)
    refine ⟨inc_lineThrough_right PPlane hCA₁,
      inc_lineThrough_left PPlane hCA₁, ?_⟩
    rw [hlines]
    exact inc_lineThrough_left PPlane hCA₂
  let L : PPlane.Line := lineThrough PPlane hAB₂
  refine ⟨T₁, T₂, hAB₁, hAB₂, hBC₁, hBC₂, hCA₁, hCA₂,
    h_diff_AB, h_diff_BC, h_diff_CA, L, ?_, ?_⟩
  · dsimp [AxialPerspective]
    refine ⟨?_, ?_, ?_⟩
    · rw [meetLines_eq_of_inc PPlane h_diff_AB p₁]
      · exact inc_lineThrough_left PPlane hAB₂
      · exact inc_lineThrough_left PPlane hAB₁
      · exact inc_lineThrough_left PPlane hAB₂
    · rw [meetLines_eq_of_inc PPlane h_diff_BC p₃]
      · exact inc_lineThrough_right PPlane hAB₂
      · exact inc_lineThrough_right PPlane hBC₁
      · exact inc_lineThrough_left PPlane hBC₂
    · rw [meetLines_eq_of_inc PPlane h_diff_CA p₁]
      · exact inc_lineThrough_left PPlane hAB₂
      · exact inc_lineThrough_right PPlane hCA₁
      · exact inc_lineThrough_right PPlane hCA₂
  · rintro ⟨O, hcentral⟩
    rcases hcentral with ⟨_, _, _, _, _, _, hAA, _⟩
    exact hAA rfl

end DesarguesProjective

#print axioms desargues_vector
#print axioms DesarguesProjective.desargues_projective_plane
#print axioms DesarguesProjective.axialPerspective_not_implies_central
