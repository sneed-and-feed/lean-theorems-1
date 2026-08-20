import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Sylvester–Gallai Theorem (Freek Wiedijk #98)

This module provides the formalization stub for the **Sylvester–Gallai Theorem**
(J. J. Sylvester 1893, T. Gallai 1944).

## Mathematical Statement
Let `S` be a finite set of points in the Euclidean plane $\mathbb{R}^2$.
If not all points in `S` lie on a single straight line (i.e. `S` is non-collinear),
then there exists an **ordinary line**—a line passing through *exactly two* points of `S`.

## References
* J. J. Sylvester (1893), *Mathematical Question 11851*, Educational Times, 59:98.
* T. Gallai (1944), *Solution to Problem 4065*, American Mathematical Monthly, 51:169–171.
* L. M. Kelly (1948), *A simple proof of the Sylvester-Gallai theorem*, in Coxeter's *Projective Geometry*.
* F. Wiedijk (2008), *Formalizing 100 Theorems*, #98.
-/

namespace SylvesterGallai

/-- A point in the 2D real affine plane. -/
abbrev Point := ℝ × ℝ

/-- Three points in the plane are collinear if the triangle they form has zero signed area. -/
def Collinear (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) = 0

/-- A finite set of points `S` is collinear if all triples in `S` are collinear. -/
def SetCollinear (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, Collinear p q r

/-- A line determined by two distinct points `p ≠ q`. -/
def lineThrough (p q : Point) : Set Point :=
  { r | Collinear p q r }

/-- An ordinary line with respect to a finite point set `S` is a line passing through
exactly two points of `S`. -/
def IsOrdinaryLine (S : Finset Point) (p q : Point) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ (∀ r ∈ S, Collinear p q r → r = p ∨ r = q)

/-- **The Sylvester–Gallai Theorem (Freek Wiedijk #98):**
Every finite, non-collinear set of points in the real Euclidean plane contains an ordinary line. -/
theorem sylvester_gallai (S : Finset Point) (h_card : 3 ≤ S.card) (h_non_collinear : ¬ SetCollinear S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ IsOrdinaryLine S p q := by
  sorry

end SylvesterGallai
