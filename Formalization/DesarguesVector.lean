import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Module

/-!
# Desargues's Theorem in Vector and Axiomatic Projective Geometry

This module develops an algebraic identity inspired by **Desargues's theorem** and an
**axiomatic projective-plane** formulation (Wiedijk #53).  The commutative-ring module identity is
a repository-specific algebraic formulation, not a verbatim rendering of the historical theorem.

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

* A. Bosse, presenting work of G. Desargues (1647/1648), *Manière universelle de Mr. Girard
  Desargues, pour pratiquer la perspective par petit-pied, comme le geometral*, cited from the
  1648 ETH Zürich edition, Rar 499, geometric propositions at the end and plate 154.
  https://doi.org/10.3931/e-rara-11184
* D. Hilbert (1899), *Grundlagen der Geometrie*, Teubner.
* H. S. M. Coxeter (1987), *Projective Geometry*, Springer-Verlag.
* J. Müller, *Projective Geometry*, §5, pp. 19–21 (nondegenerate forward and converse forms).
  https://www.math.rwth-aachen.de/~Juergen.Mueller/preprints/jm114.pdf
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

private lemma lineThrough_eq_of_inc (PPlane : ProjectivePlane)
    {p q : PPlane.Point} (hpq : p ≠ q) (l : PPlane.Line)
    (hp : PPlane.Inc p l) (hq : PPlane.Inc q l) :
    lineThrough PPlane hpq = l := by
  apply (PPlane.line_through p q hpq).unique
  · exact (PPlane.line_through p q hpq).choose_spec.1
  · exact ⟨hp, hq⟩

private lemma inc_meetLines_left (PPlane : ProjectivePlane)
    {l₁ l₂ : PPlane.Line} (hl : l₁ ≠ l₂) :
    PPlane.Inc (meetLines PPlane hl) l₁ :=
  (PPlane.point_intersection l₁ l₂ hl).choose_spec.1.1

private lemma inc_meetLines_right (PPlane : ProjectivePlane)
    {l₁ l₂ : PPlane.Line} (hl : l₁ ≠ l₂) :
    PPlane.Inc (meetLines PPlane hl) l₂ :=
  (PPlane.point_intersection l₁ l₂ hl).choose_spec.1.2

private lemma meetLines_eq_of_inc (PPlane : ProjectivePlane)
    {l₁ l₂ : PPlane.Line} (hl : l₁ ≠ l₂) (p : PPlane.Point)
    (hp₁ : PPlane.Inc p l₁) (hp₂ : PPlane.Inc p l₂) :
    meetLines PPlane hl = p := by
  apply (PPlane.point_intersection l₁ l₂ hl).unique
  · exact (PPlane.point_intersection l₁ l₂ hl).choose_spec.1
  · exact ⟨hp₁, hp₂⟩

private lemma point_eq_of_inc_two_lines (PPlane : ProjectivePlane)
    {l₁ l₂ : PPlane.Line} (hl : l₁ ≠ l₂) {p q : PPlane.Point}
    (hp₁ : PPlane.Inc p l₁) (hp₂ : PPlane.Inc p l₂)
    (hq₁ : PPlane.Inc q l₁) (hq₂ : PPlane.Inc q l₂) : p = q := by
  rw [← meetLines_eq_of_inc PPlane hl p hp₁ hp₂,
    ← meetLines_eq_of_inc PPlane hl q hq₁ hq₂]

private lemma line_eq_of_inc_two_points (PPlane : ProjectivePlane)
    {p q : PPlane.Point} (hpq : p ≠ q) {l₁ l₂ : PPlane.Line}
    (hp₁ : PPlane.Inc p l₁) (hq₁ : PPlane.Inc q l₁)
    (hp₂ : PPlane.Inc p l₂) (hq₂ : PPlane.Inc q l₂) : l₁ = l₂ := by
  rw [← lineThrough_eq_of_inc PPlane hpq l₁ hp₁ hq₁,
    ← lineThrough_eq_of_inc PPlane hpq l₂ hp₂ hq₂]

-- ============================================================================
-- Section 3: Projective Triangles and Perspectives
-- ============================================================================

/-- A projective triangle is a triple of non-collinear points. -/
structure Triangle (PPlane : ProjectivePlane) where
  A : PPlane.Point
  B : PPlane.Point
  C : PPlane.Point
  h_non_collinear : ¬ Collinear PPlane A B C

private lemma triangle_side_lines_ne (PPlane : ProjectivePlane) (T : Triangle PPlane)
    (hAB : T.A ≠ T.B) (hBC : T.B ≠ T.C) (hCA : T.C ≠ T.A) :
    lineThrough PPlane hAB ≠ lineThrough PPlane hBC ∧
      lineThrough PPlane hBC ≠ lineThrough PPlane hCA ∧
      lineThrough PPlane hCA ≠ lineThrough PPlane hAB := by
  refine ⟨?_, ?_, ?_⟩
  · intro hlines
    apply T.h_non_collinear
    refine ⟨lineThrough PPlane hAB, inc_lineThrough_left PPlane hAB,
      inc_lineThrough_right PPlane hAB, ?_⟩
    rw [hlines]
    exact inc_lineThrough_right PPlane hBC
  · intro hlines
    apply T.h_non_collinear
    refine ⟨lineThrough PPlane hBC, ?_, inc_lineThrough_left PPlane hBC,
      inc_lineThrough_right PPlane hBC⟩
    rw [hlines]
    exact inc_lineThrough_right PPlane hCA
  · intro hlines
    apply T.h_non_collinear
    refine ⟨lineThrough PPlane hCA, inc_lineThrough_right PPlane hCA, ?_,
      inc_lineThrough_left PPlane hCA⟩
    rw [hlines]
    exact inc_lineThrough_right PPlane hAB

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

/-- A nondegenerate axial perspectivity.  Besides the three corresponding side
    intersections lying on `L`, the axis is required not to be a side of either
    triangle.  These six exclusions are dual to requiring the center of a
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

/-- **Forward Desargues axiom in projective geometry (Bosse/Desargues 1647/1648):**
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

/-- **Converse Desargues theorem, with the nondegeneracy dual to
    `CentralPerspective`:** in a Desarguesian plane, a proper axial perspectivity
    and distinct corresponding vertices determine a central perspectivity.

The proof applies forward Desargues to the derived triangles `(R, A₁, A₂)` and
`(Q, B₁, B₂)`, centrally perspective from `P`.  Their corresponding side
intersections are `C₁`, the intersection `O` of `A₁A₂` and `B₁B₂`, and `C₂`.
Thus `C₁`, `O`, and `C₂` are collinear. -/
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
    ∃ O : PPlane.Point, CentralPerspective PPlane T₁ T₂ O := by
  rcases h_proper with
    ⟨h_axial, hL_AB₁, hL_BC₁, hL_CA₁, hL_AB₂, hL_BC₂, hL_CA₂⟩
  rcases triangle_side_lines_ne PPlane T₁ hAB₁ hBC₁ hCA₁ with
    ⟨hAB_BC₁, hBC_CA₁, hCA_AB₁⟩
  rcases triangle_side_lines_ne PPlane T₂ hAB₂ hBC₂ hCA₂ with
    ⟨hAB_BC₂, hBC_CA₂, hCA_AB₂⟩
  let P : PPlane.Point := meetLines PPlane h_diff_AB
  let Q : PPlane.Point := meetLines PPlane h_diff_BC
  let R : PPlane.Point := meetLines PPlane h_diff_CA
  have hP_AB₁ : PPlane.Inc P (lineThrough PPlane hAB₁) := by
    dsimp [P]
    exact inc_meetLines_left PPlane h_diff_AB
  have hP_AB₂ : PPlane.Inc P (lineThrough PPlane hAB₂) := by
    dsimp [P]
    exact inc_meetLines_right PPlane h_diff_AB
  have hQ_BC₁ : PPlane.Inc Q (lineThrough PPlane hBC₁) := by
    dsimp [Q]
    exact inc_meetLines_left PPlane h_diff_BC
  have hQ_BC₂ : PPlane.Inc Q (lineThrough PPlane hBC₂) := by
    dsimp [Q]
    exact inc_meetLines_right PPlane h_diff_BC
  have hR_CA₁ : PPlane.Inc R (lineThrough PPlane hCA₁) := by
    dsimp [R]
    exact inc_meetLines_left PPlane h_diff_CA
  have hR_CA₂ : PPlane.Inc R (lineThrough PPlane hCA₂) := by
    dsimp [R]
    exact inc_meetLines_right PPlane h_diff_CA
  have h_axis : PPlane.Inc P L ∧ PPlane.Inc Q L ∧ PPlane.Inc R L := by
    simpa only [AxialPerspective, P, Q, R] using h_axial
  rcases h_axis with ⟨hP_L, hQ_L, hR_L⟩
  have hPQ : P ≠ Q := by
    intro h_eq
    have hP_BC₁ : PPlane.Inc P (lineThrough PPlane hBC₁) := by
      rw [h_eq]
      exact hQ_BC₁
    have hP_BC₂ : PPlane.Inc P (lineThrough PPlane hBC₂) := by
      rw [h_eq]
      exact hQ_BC₂
    have hP_B₁ : P = T₁.B :=
      point_eq_of_inc_two_lines PPlane hAB_BC₁ hP_AB₁ hP_BC₁
        (inc_lineThrough_right PPlane hAB₁) (inc_lineThrough_left PPlane hBC₁)
    have hP_B₂ : P = T₂.B :=
      point_eq_of_inc_two_lines PPlane hAB_BC₂ hP_AB₂ hP_BC₂
        (inc_lineThrough_right PPlane hAB₂) (inc_lineThrough_left PPlane hBC₂)
    exact hBB (hP_B₁.symm.trans hP_B₂)
  have hQR : Q ≠ R := by
    intro h_eq
    have hQ_CA₁ : PPlane.Inc Q (lineThrough PPlane hCA₁) := by
      rw [h_eq]
      exact hR_CA₁
    have hQ_CA₂ : PPlane.Inc Q (lineThrough PPlane hCA₂) := by
      rw [h_eq]
      exact hR_CA₂
    have hQ_C₁ : Q = T₁.C :=
      point_eq_of_inc_two_lines PPlane hBC_CA₁ hQ_BC₁ hQ_CA₁
        (inc_lineThrough_right PPlane hBC₁) (inc_lineThrough_left PPlane hCA₁)
    have hQ_C₂ : Q = T₂.C :=
      point_eq_of_inc_two_lines PPlane hBC_CA₂ hQ_BC₂ hQ_CA₂
        (inc_lineThrough_right PPlane hBC₂) (inc_lineThrough_left PPlane hCA₂)
    exact hCC (hQ_C₁.symm.trans hQ_C₂)
  have hRP : R ≠ P := by
    intro h_eq
    have hR_AB₁ : PPlane.Inc R (lineThrough PPlane hAB₁) := by
      rw [h_eq]
      exact hP_AB₁
    have hR_AB₂ : PPlane.Inc R (lineThrough PPlane hAB₂) := by
      rw [h_eq]
      exact hP_AB₂
    have hR_A₁ : R = T₁.A :=
      point_eq_of_inc_two_lines PPlane hCA_AB₁ hR_CA₁ hR_AB₁
        (inc_lineThrough_right PPlane hCA₁) (inc_lineThrough_left PPlane hAB₁)
    have hR_A₂ : R = T₂.A :=
      point_eq_of_inc_two_lines PPlane hCA_AB₂ hR_CA₂ hR_AB₂
        (inc_lineThrough_right PPlane hCA₂) (inc_lineThrough_left PPlane hAB₂)
    exact hAA (hR_A₁.symm.trans hR_A₂)
  have hP_A₁ : P ≠ T₁.A := by
    intro h_eq
    have hAR : T₁.A ≠ R := fun h => hRP (h.symm.trans h_eq.symm)
    apply hL_CA₁
    exact line_eq_of_inc_two_points PPlane hAR (h_eq ▸ hP_L) hR_L
      (inc_lineThrough_right PPlane hCA₁) hR_CA₁
  have hP_A₂ : P ≠ T₂.A := by
    intro h_eq
    have hAR : T₂.A ≠ R := fun h => hRP (h.symm.trans h_eq.symm)
    apply hL_CA₂
    exact line_eq_of_inc_two_points PPlane hAR (h_eq ▸ hP_L) hR_L
      (inc_lineThrough_right PPlane hCA₂) hR_CA₂
  have hP_B₁ : P ≠ T₁.B := by
    intro h_eq
    have hBQ : T₁.B ≠ Q := fun h => hPQ (h_eq.trans h)
    apply hL_BC₁
    exact line_eq_of_inc_two_points PPlane hBQ (h_eq ▸ hP_L) hQ_L
      (inc_lineThrough_left PPlane hBC₁) hQ_BC₁
  have hP_B₂ : P ≠ T₂.B := by
    intro h_eq
    have hBQ : T₂.B ≠ Q := fun h => hPQ (h_eq.trans h)
    apply hL_BC₂
    exact line_eq_of_inc_two_points PPlane hBQ (h_eq ▸ hP_L) hQ_L
      (inc_lineThrough_left PPlane hBC₂) hQ_BC₂
  have hR_A₁ : R ≠ T₁.A := by
    intro h_eq
    have hR_AB₁ : PPlane.Inc R (lineThrough PPlane hAB₁) := by
      rw [h_eq]
      exact inc_lineThrough_left PPlane hAB₁
    apply hL_AB₁
    exact line_eq_of_inc_two_points PPlane hRP hR_L hP_L hR_AB₁ hP_AB₁
  have hR_A₂ : R ≠ T₂.A := by
    intro h_eq
    have hR_AB₂ : PPlane.Inc R (lineThrough PPlane hAB₂) := by
      rw [h_eq]
      exact inc_lineThrough_left PPlane hAB₂
    apply hL_AB₂
    exact line_eq_of_inc_two_points PPlane hRP hR_L hP_L hR_AB₂ hP_AB₂
  have hQ_B₁ : Q ≠ T₁.B := by
    intro h_eq
    have hQ_AB₁ : PPlane.Inc Q (lineThrough PPlane hAB₁) := by
      rw [h_eq]
      exact inc_lineThrough_right PPlane hAB₁
    apply hL_AB₁
    exact line_eq_of_inc_two_points PPlane hPQ hP_L hQ_L hP_AB₁ hQ_AB₁
  have hQ_B₂ : Q ≠ T₂.B := by
    intro h_eq
    have hQ_AB₂ : PPlane.Inc Q (lineThrough PPlane hAB₂) := by
      rw [h_eq]
      exact inc_lineThrough_right PPlane hAB₂
    apply hL_AB₂
    exact line_eq_of_inc_two_points PPlane hPQ hP_L hQ_L hP_AB₂ hQ_AB₂
  let U₁ : Triangle PPlane :=
    { A := R
      B := T₁.A
      C := T₂.A
      h_non_collinear := by
        rintro ⟨m, hRm, hA₁m, hA₂m⟩
        have hm_CA₁ : m = lineThrough PPlane hCA₁ :=
          line_eq_of_inc_two_points PPlane hR_A₁ hRm hA₁m hR_CA₁
            (inc_lineThrough_right PPlane hCA₁)
        have hm_CA₂ : m = lineThrough PPlane hCA₂ :=
          line_eq_of_inc_two_points PPlane hR_A₂ hRm hA₂m hR_CA₂
            (inc_lineThrough_right PPlane hCA₂)
        exact h_diff_CA (hm_CA₁.symm.trans hm_CA₂) }
  let U₂ : Triangle PPlane :=
    { A := Q
      B := T₁.B
      C := T₂.B
      h_non_collinear := by
        rintro ⟨m, hQm, hB₁m, hB₂m⟩
        have hm_BC₁ : m = lineThrough PPlane hBC₁ :=
          line_eq_of_inc_two_points PPlane hQ_B₁ hQm hB₁m hQ_BC₁
            (inc_lineThrough_left PPlane hBC₁)
        have hm_BC₂ : m = lineThrough PPlane hBC₂ :=
          line_eq_of_inc_two_points PPlane hQ_B₂ hQm hB₂m hQ_BC₂
            (inc_lineThrough_left PPlane hBC₂)
        exact h_diff_BC (hm_BC₁.symm.trans hm_BC₂) }
  have hUAB₁ : U₁.A ≠ U₁.B := by simpa [U₁] using hR_A₁
  have hUAB₂ : U₂.A ≠ U₂.B := by simpa [U₂] using hQ_B₁
  have hUBC₁ : U₁.B ≠ U₁.C := by simpa [U₁] using hAA
  have hUBC₂ : U₂.B ≠ U₂.C := by simpa [U₂] using hBB
  have hUCA₁ : U₁.C ≠ U₁.A := by simpa [U₁] using hR_A₂.symm
  have hUCA₂ : U₂.C ≠ U₂.A := by simpa [U₂] using hQ_B₂.symm
  have h_central_U : CentralPerspective PPlane U₁ U₂ P := by
    refine ⟨hRP.symm, hPQ, hP_A₁, hP_B₁, hP_A₂, hP_B₂, hQR.symm,
      hAB₁, hAB₂, ?_, ?_, ?_⟩
    · exact ⟨L, hP_L, hR_L, hQ_L⟩
    · exact ⟨lineThrough PPlane hAB₁, hP_AB₁,
        inc_lineThrough_left PPlane hAB₁, inc_lineThrough_right PPlane hAB₁⟩
    · exact ⟨lineThrough PPlane hAB₂, hP_AB₂,
        inc_lineThrough_left PPlane hAB₂, inc_lineThrough_right PPlane hAB₂⟩
  have hRA : lineThrough PPlane hUAB₁ = lineThrough PPlane hCA₁ :=
    lineThrough_eq_of_inc PPlane hUAB₁ (lineThrough PPlane hCA₁) hR_CA₁
      (inc_lineThrough_right PPlane hCA₁)
  have hQB : lineThrough PPlane hUAB₂ = lineThrough PPlane hBC₁ :=
    lineThrough_eq_of_inc PPlane hUAB₂ (lineThrough PPlane hBC₁) hQ_BC₁
      (inc_lineThrough_left PPlane hBC₁)
  have h_diff_UAB : lineThrough PPlane hUAB₁ ≠ lineThrough PPlane hUAB₂ := by
    intro h_eq
    exact hBC_CA₁.symm (hRA.symm.trans (h_eq.trans hQB))
  have h_diff_UBC : lineThrough PPlane hUBC₁ ≠ lineThrough PPlane hUBC₂ := by
    intro h_eq
    have hB₁_U₁ : PPlane.Inc T₁.B (lineThrough PPlane hUBC₁) := by
      rw [h_eq]
      exact inc_lineThrough_left PPlane hUBC₂
    have hB₂_U₁ : PPlane.Inc T₂.B (lineThrough PPlane hUBC₁) := by
      rw [h_eq]
      exact inc_lineThrough_right PPlane hUBC₂
    have hAB₁_eq : lineThrough PPlane hAB₁ = lineThrough PPlane hUBC₁ :=
      lineThrough_eq_of_inc PPlane hAB₁ _ (inc_lineThrough_left PPlane hUBC₁) hB₁_U₁
    have hAB₂_eq : lineThrough PPlane hAB₂ = lineThrough PPlane hUBC₁ :=
      lineThrough_eq_of_inc PPlane hAB₂ _ (inc_lineThrough_right PPlane hUBC₁) hB₂_U₁
    exact h_diff_AB (hAB₁_eq.trans hAB₂_eq.symm)
  have hA₂R : lineThrough PPlane hUCA₁ = lineThrough PPlane hCA₂ :=
    lineThrough_eq_of_inc PPlane hUCA₁ (lineThrough PPlane hCA₂)
      (inc_lineThrough_right PPlane hCA₂) hR_CA₂
  have hB₂Q : lineThrough PPlane hUCA₂ = lineThrough PPlane hBC₂ :=
    lineThrough_eq_of_inc PPlane hUCA₂ (lineThrough PPlane hBC₂)
      (inc_lineThrough_left PPlane hBC₂) hQ_BC₂
  have h_diff_UCA : lineThrough PPlane hUCA₁ ≠ lineThrough PPlane hUCA₂ := by
    intro h_eq
    exact hBC_CA₂.symm (hA₂R.symm.trans (h_eq.trans hB₂Q))
  obtain ⟨M, hM⟩ := h_des U₁ U₂ P h_central_U hUAB₁ hUAB₂ hUBC₁ hUBC₂
    hUCA₁ hUCA₂ h_diff_UAB h_diff_UBC h_diff_UCA
  rcases hM with ⟨hC₁M, hOM, hC₂M⟩
  have hmeet_C₁ : meetLines PPlane h_diff_UAB = T₁.C := by
    apply meetLines_eq_of_inc PPlane h_diff_UAB
    · rw [hRA]
      exact inc_lineThrough_left PPlane hCA₁
    · rw [hQB]
      exact inc_lineThrough_right PPlane hBC₁
  have hmeet_C₂ : meetLines PPlane h_diff_UCA = T₂.C := by
    apply meetLines_eq_of_inc PPlane h_diff_UCA
    · rw [hA₂R]
      exact inc_lineThrough_left PPlane hCA₂
    · rw [hB₂Q]
      exact inc_lineThrough_right PPlane hBC₂
  rw [hmeet_C₁] at hC₁M
  rw [hmeet_C₂] at hC₂M
  let O : PPlane.Point := meetLines PPlane h_diff_UBC
  have hO_AA : PPlane.Inc O (lineThrough PPlane hUBC₁) := by
    dsimp [O]
    exact inc_meetLines_left PPlane h_diff_UBC
  have hO_BB : PPlane.Inc O (lineThrough PPlane hUBC₂) := by
    dsimp [O]
    exact inc_meetLines_right PPlane h_diff_UBC
  have hO_M : PPlane.Inc O M := by simpa only [O] using hOM
  have hcol_AA : Collinear PPlane O T₁.A T₂.A :=
    ⟨lineThrough PPlane hUBC₁, hO_AA, inc_lineThrough_left PPlane hUBC₁,
      inc_lineThrough_right PPlane hUBC₁⟩
  have hcol_BB : Collinear PPlane O T₁.B T₂.B :=
    ⟨lineThrough PPlane hUBC₂, hO_BB, inc_lineThrough_left PPlane hUBC₂,
      inc_lineThrough_right PPlane hUBC₂⟩
  have hcol_CC : Collinear PPlane O T₁.C T₂.C := ⟨M, hO_M, hC₁M, hC₂M⟩
  have hO_A₁ : O ≠ T₁.A := by
    intro h_eq
    have hA₁_BB : PPlane.Inc T₁.A (lineThrough PPlane hUBC₂) := by
      rw [← h_eq]
      exact hO_BB
    have hAB₁_BB : lineThrough PPlane hAB₁ = lineThrough PPlane hUBC₂ :=
      line_eq_of_inc_two_points PPlane hAB₁ (inc_lineThrough_left PPlane hAB₁)
        (inc_lineThrough_right PPlane hAB₁) hA₁_BB
        (inc_lineThrough_left PPlane hUBC₂)
    have hB₂_AB₁ : PPlane.Inc T₂.B (lineThrough PPlane hAB₁) := by
      rw [hAB₁_BB]
      exact inc_lineThrough_right PPlane hUBC₂
    have hP_B₂_eq : P = T₂.B := by
      simpa only [P] using meetLines_eq_of_inc PPlane h_diff_AB T₂.B hB₂_AB₁
        (inc_lineThrough_right PPlane hAB₂)
    have hA₁_M : PPlane.Inc T₁.A M := by
      rw [← h_eq]
      exact hO_M
    have hCA₁_M : lineThrough PPlane hCA₁ = M :=
      line_eq_of_inc_two_points PPlane hCA₁ (inc_lineThrough_left PPlane hCA₁)
        (inc_lineThrough_right PPlane hCA₁) hC₁M hA₁_M
    have hC₂_CA₁ : PPlane.Inc T₂.C (lineThrough PPlane hCA₁) := by
      rw [hCA₁_M]
      exact hC₂M
    have hR_C₂_eq : R = T₂.C := by
      simpa only [R] using meetLines_eq_of_inc PPlane h_diff_CA T₂.C hC₂_CA₁
        (inc_lineThrough_left PPlane hCA₂)
    apply hL_BC₂
    exact line_eq_of_inc_two_points PPlane hBC₂ (hP_B₂_eq ▸ hP_L)
      (hR_C₂_eq ▸ hR_L) (inc_lineThrough_left PPlane hBC₂)
      (inc_lineThrough_right PPlane hBC₂)
  have hO_A₂ : O ≠ T₂.A := by
    intro h_eq
    have hA₂_BB : PPlane.Inc T₂.A (lineThrough PPlane hUBC₂) := by
      rw [← h_eq]
      exact hO_BB
    have hAB₂_BB : lineThrough PPlane hAB₂ = lineThrough PPlane hUBC₂ :=
      line_eq_of_inc_two_points PPlane hAB₂ (inc_lineThrough_left PPlane hAB₂)
        (inc_lineThrough_right PPlane hAB₂) hA₂_BB
        (inc_lineThrough_right PPlane hUBC₂)
    have hB₁_AB₂ : PPlane.Inc T₁.B (lineThrough PPlane hAB₂) := by
      rw [hAB₂_BB]
      exact inc_lineThrough_left PPlane hUBC₂
    have hP_B₁_eq : P = T₁.B := by
      simpa only [P] using meetLines_eq_of_inc PPlane h_diff_AB T₁.B
        (inc_lineThrough_right PPlane hAB₁) hB₁_AB₂
    have hA₂_M : PPlane.Inc T₂.A M := by
      rw [← h_eq]
      exact hO_M
    have hCA₂_M : lineThrough PPlane hCA₂ = M :=
      line_eq_of_inc_two_points PPlane hCA₂ (inc_lineThrough_left PPlane hCA₂)
        (inc_lineThrough_right PPlane hCA₂) hC₂M hA₂_M
    have hC₁_CA₂ : PPlane.Inc T₁.C (lineThrough PPlane hCA₂) := by
      rw [hCA₂_M]
      exact hC₁M
    have hR_C₁_eq : R = T₁.C := by
      simpa only [R] using meetLines_eq_of_inc PPlane h_diff_CA T₁.C
        (inc_lineThrough_left PPlane hCA₁) hC₁_CA₂
    apply hL_BC₁
    exact line_eq_of_inc_two_points PPlane hBC₁ (hP_B₁_eq ▸ hP_L)
      (hR_C₁_eq ▸ hR_L) (inc_lineThrough_left PPlane hBC₁)
      (inc_lineThrough_right PPlane hBC₁)
  have hO_B₁ : O ≠ T₁.B := by
    intro h_eq
    have hB₁_AA : PPlane.Inc T₁.B (lineThrough PPlane hUBC₁) := by
      rw [← h_eq]
      exact hO_AA
    have hAB₁_AA : lineThrough PPlane hAB₁ = lineThrough PPlane hUBC₁ :=
      line_eq_of_inc_two_points PPlane hAB₁ (inc_lineThrough_left PPlane hAB₁)
        (inc_lineThrough_right PPlane hAB₁) (inc_lineThrough_left PPlane hUBC₁) hB₁_AA
    have hA₂_AB₁ : PPlane.Inc T₂.A (lineThrough PPlane hAB₁) := by
      rw [hAB₁_AA]
      exact inc_lineThrough_right PPlane hUBC₁
    have hP_A₂_eq : P = T₂.A := by
      simpa only [P] using meetLines_eq_of_inc PPlane h_diff_AB T₂.A hA₂_AB₁
        (inc_lineThrough_left PPlane hAB₂)
    have hB₁_M : PPlane.Inc T₁.B M := by
      rw [← h_eq]
      exact hO_M
    have hBC₁_M : lineThrough PPlane hBC₁ = M :=
      line_eq_of_inc_two_points PPlane hBC₁ (inc_lineThrough_left PPlane hBC₁)
        (inc_lineThrough_right PPlane hBC₁) hB₁_M hC₁M
    have hC₂_BC₁ : PPlane.Inc T₂.C (lineThrough PPlane hBC₁) := by
      rw [hBC₁_M]
      exact hC₂M
    have hQ_C₂_eq : Q = T₂.C := by
      simpa only [Q] using meetLines_eq_of_inc PPlane h_diff_BC T₂.C hC₂_BC₁
        (inc_lineThrough_right PPlane hBC₂)
    apply hL_CA₂
    exact line_eq_of_inc_two_points PPlane hCA₂ (hQ_C₂_eq ▸ hQ_L)
      (hP_A₂_eq ▸ hP_L) (inc_lineThrough_left PPlane hCA₂)
      (inc_lineThrough_right PPlane hCA₂)
  have hO_B₂ : O ≠ T₂.B := by
    intro h_eq
    have hB₂_AA : PPlane.Inc T₂.B (lineThrough PPlane hUBC₁) := by
      rw [← h_eq]
      exact hO_AA
    have hAB₂_AA : lineThrough PPlane hAB₂ = lineThrough PPlane hUBC₁ :=
      line_eq_of_inc_two_points PPlane hAB₂ (inc_lineThrough_left PPlane hAB₂)
        (inc_lineThrough_right PPlane hAB₂) (inc_lineThrough_right PPlane hUBC₁) hB₂_AA
    have hA₁_AB₂ : PPlane.Inc T₁.A (lineThrough PPlane hAB₂) := by
      rw [hAB₂_AA]
      exact inc_lineThrough_left PPlane hUBC₁
    have hP_A₁_eq : P = T₁.A := by
      simpa only [P] using meetLines_eq_of_inc PPlane h_diff_AB T₁.A
        (inc_lineThrough_left PPlane hAB₁) hA₁_AB₂
    have hB₂_M : PPlane.Inc T₂.B M := by
      rw [← h_eq]
      exact hO_M
    have hBC₂_M : lineThrough PPlane hBC₂ = M :=
      line_eq_of_inc_two_points PPlane hBC₂ (inc_lineThrough_left PPlane hBC₂)
        (inc_lineThrough_right PPlane hBC₂) hB₂_M hC₂M
    have hC₁_BC₂ : PPlane.Inc T₁.C (lineThrough PPlane hBC₂) := by
      rw [hBC₂_M]
      exact hC₁M
    have hQ_C₁_eq : Q = T₁.C := by
      simpa only [Q] using meetLines_eq_of_inc PPlane h_diff_BC T₁.C
        (inc_lineThrough_right PPlane hBC₁) hC₁_BC₂
    apply hL_CA₁
    exact line_eq_of_inc_two_points PPlane hCA₁ (hQ_C₁_eq ▸ hQ_L)
      (hP_A₁_eq ▸ hP_L) (inc_lineThrough_left PPlane hCA₁)
      (inc_lineThrough_right PPlane hCA₁)
  have hO_C₁ : O ≠ T₁.C := by
    intro h_eq
    have hC₁_BB : PPlane.Inc T₁.C (lineThrough PPlane hUBC₂) := by
      rw [← h_eq]
      exact hO_BB
    have hBC₁_BB : lineThrough PPlane hBC₁ = lineThrough PPlane hUBC₂ :=
      line_eq_of_inc_two_points PPlane hBC₁ (inc_lineThrough_left PPlane hBC₁)
        (inc_lineThrough_right PPlane hBC₁) (inc_lineThrough_left PPlane hUBC₂) hC₁_BB
    have hB₂_BC₁ : PPlane.Inc T₂.B (lineThrough PPlane hBC₁) := by
      rw [hBC₁_BB]
      exact inc_lineThrough_right PPlane hUBC₂
    have hQ_B₂_eq : Q = T₂.B := by
      simpa only [Q] using meetLines_eq_of_inc PPlane h_diff_BC T₂.B hB₂_BC₁
        (inc_lineThrough_left PPlane hBC₂)
    have hC₁_AA : PPlane.Inc T₁.C (lineThrough PPlane hUBC₁) := by
      rw [← h_eq]
      exact hO_AA
    have hCA₁_AA : lineThrough PPlane hCA₁ = lineThrough PPlane hUBC₁ :=
      line_eq_of_inc_two_points PPlane hCA₁ (inc_lineThrough_left PPlane hCA₁)
        (inc_lineThrough_right PPlane hCA₁) hC₁_AA (inc_lineThrough_left PPlane hUBC₁)
    have hA₂_CA₁ : PPlane.Inc T₂.A (lineThrough PPlane hCA₁) := by
      rw [hCA₁_AA]
      exact inc_lineThrough_right PPlane hUBC₁
    have hR_A₂_eq : R = T₂.A := by
      simpa only [R] using meetLines_eq_of_inc PPlane h_diff_CA T₂.A hA₂_CA₁
        (inc_lineThrough_right PPlane hCA₂)
    apply hL_AB₂
    exact line_eq_of_inc_two_points PPlane hAB₂ (hR_A₂_eq ▸ hR_L)
      (hQ_B₂_eq ▸ hQ_L) (inc_lineThrough_left PPlane hAB₂)
      (inc_lineThrough_right PPlane hAB₂)
  have hO_C₂ : O ≠ T₂.C := by
    intro h_eq
    have hC₂_BB : PPlane.Inc T₂.C (lineThrough PPlane hUBC₂) := by
      rw [← h_eq]
      exact hO_BB
    have hBC₂_BB : lineThrough PPlane hBC₂ = lineThrough PPlane hUBC₂ :=
      line_eq_of_inc_two_points PPlane hBC₂ (inc_lineThrough_left PPlane hBC₂)
        (inc_lineThrough_right PPlane hBC₂) (inc_lineThrough_right PPlane hUBC₂) hC₂_BB
    have hB₁_BC₂ : PPlane.Inc T₁.B (lineThrough PPlane hBC₂) := by
      rw [hBC₂_BB]
      exact inc_lineThrough_left PPlane hUBC₂
    have hQ_B₁_eq : Q = T₁.B := by
      simpa only [Q] using meetLines_eq_of_inc PPlane h_diff_BC T₁.B
        (inc_lineThrough_left PPlane hBC₁) hB₁_BC₂
    have hC₂_AA : PPlane.Inc T₂.C (lineThrough PPlane hUBC₁) := by
      rw [← h_eq]
      exact hO_AA
    have hCA₂_AA : lineThrough PPlane hCA₂ = lineThrough PPlane hUBC₁ :=
      line_eq_of_inc_two_points PPlane hCA₂ (inc_lineThrough_left PPlane hCA₂)
        (inc_lineThrough_right PPlane hCA₂) hC₂_AA (inc_lineThrough_right PPlane hUBC₁)
    have hA₁_CA₂ : PPlane.Inc T₁.A (lineThrough PPlane hCA₂) := by
      rw [hCA₂_AA]
      exact inc_lineThrough_left PPlane hUBC₁
    have hR_A₁_eq : R = T₁.A := by
      simpa only [R] using meetLines_eq_of_inc PPlane h_diff_CA T₁.A
        (inc_lineThrough_right PPlane hCA₁) hA₁_CA₂
    apply hL_AB₁
    exact line_eq_of_inc_two_points PPlane hAB₁ (hR_A₁_eq ▸ hR_L)
      (hQ_B₁_eq ▸ hQ_L) (inc_lineThrough_left PPlane hAB₁)
      (inc_lineThrough_right PPlane hAB₁)
  exact ⟨O, hO_A₁, hO_A₂, hO_B₁, hO_B₂, hO_C₁, hO_C₂,
    hAA, hBB, hCC, hcol_AA, hcol_BB, hcol_CC⟩

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
#print axioms DesarguesProjective.desargues_converse_projective_plane
#print axioms DesarguesProjective.axialPerspective_not_implies_central
