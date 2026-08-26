import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace SylvesterGallai

/-- A point in the 2D real affine plane. -/
abbrev Point := ℝ × ℝ

/-- Three points in the plane are collinear if the triangle they form has zero signed area. -/
def Collinear (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) = 0

/-- A finite set of points `S` is collinear if all triples in `S` are collinear. -/
def SetCollinear (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, Collinear p q r

/-- An ordinary line with respect to a finite point set `S` is a line passing through
exactly two points of `S`. -/
def IsOrdinaryLine (S : Finset Point) (p q : Point) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ (∀ r ∈ S, Collinear p q r → r = p ∨ r = q)

/-- **The Sylvester–Gallai Theorem (Freek Wiedijk #98):**
Every finite, non-collinear set of points in the real Euclidean plane contains an ordinary line. -/
theorem sylvester_gallai (S : Finset Point) (_h_card : 3 ≤ S.card) (h_non_collinear : ¬ SetCollinear S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ IsOrdinaryLine S p q := sorry

end SylvesterGallai
