import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Convex.Hull

open Finset

/-- A point in the 2D Euclidean plane. -/
abbrev Point2D := ℝ × ℝ

/-- Signed area / orientation determinant of three points `p, q, r`. -/
def orientationDet (p q r : Point2D) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- Predicate asserting that a set of points is in general position (no three points collinear). -/
def InGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p q r, p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → p ≠ r →
    orientationDet p q r ≠ 0

/-- Predicate asserting that a set of points has mutually distinct x-coordinates. -/
def HasDistinctX (S : Finset Point2D) : Prop :=
  ∀ p q, p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1

/-- Predicate asserting that a subset of k points forms the vertex set of a strictly convex k-gon. -/
def FormsConvexPolygon (S : Finset Point2D) (k : ℕ) : Prop :=
  ∃ (poly : Finset Point2D), poly ⊆ S ∧ poly.card = k ∧
    ∀ p ∈ poly, p ∉ convexHull ℝ (poly \ {p} : Set Point2D)

/-- The Erdős–Szekeres upper bound: ES(k) ≤ Nat.choose (2*k - 4) (k - 2) + 1. -/
def erdosSzekeresBound (k : ℕ) : ℕ :=
  Nat.choose (2 * k - 4) (k - 2) + 1

/-- **The Erdős–Szekeres Convex Polygon Theorem / Happy Ending Theorem (1935)**:
Every set of at least `erdosSzekeresBound k` points in general position in ℝ² with distinct x-coordinates
contains the vertices of a strictly convex k-gon. -/
theorem erdos_szekeres_convex_polygon (k : ℕ) (hk : 3 ≤ k)
    (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : erdosSzekeresBound k ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S k := sorry
