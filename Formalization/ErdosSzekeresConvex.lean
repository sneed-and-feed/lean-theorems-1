import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The Happy Ending Theorem (Erdős–Szekeres Convex Polygon Theorem, 1935)

**The Happy Ending Theorem (Paul Erdős & George Szekeres, 1935)**
is one of the founding results of modern discrete and combinatorial geometry.

## Mathematical Statement
For every integer $k \ge 3$, there exists a smallest integer $ES(k)$ such that any set
of at least $ES(k)$ points in the Euclidean plane $\mathbb{R}^2$ in **general position**
(no three points collinear) contains the vertices of a convex $k$-gon.

Erdős and Szekeres proved the exact bound:
$$ES(k) \le \binom{2k - 4}{k - 2} + 1$$
and conjectured the exact value is $ES(k) = 2^{k - 2} + 1$:
- $k = 4 \implies ES(4) = 5$ (Esther Klein's original problem)
- $k = 5 \implies ES(5) = 9$ (Kalbfleisch et al. 1970 / Makai)
- $k = 6 \implies ES(6) = 17$ (Szekeres & Peters 2006).

## Proof Technique (Cups and Caps / Ramsey Transition)
1. **Esther Klein Base Case ($k = 4$):** Among any 5 points in general position,
   either 4 form a convex quadrilateral directly, or the convex hull is a triangle containing
   2 interior points whose connecting line separates two of the triangle's vertices,
   forming a convex quad with the remaining vertices.
2. **Cup-Cap Lemma:** A sequence of points $(x_1, y_1), \dots, (x_m, y_m)$ sorted by $x$-coordinate
   forms an $a$-cup (convex downward) or a $b$-cap (convex upward).
   Any set of $\binom{a+b-4}{a-2} + 1$ points in general position contains an $a$-cup or a $b$-cap.
-/

-- ============================================================================
-- Section 1: General Position & Planar Convex Hulls
-- ============================================================================

/-- A point in the 2D Euclidean plane. -/
abbrev Point2D := ℝ × ℝ

/-- Predicate asserting that a set of points is in general position (no three points collinear). -/
def InGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p q r, p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → p ≠ r →
    (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) ≠ 0

/-- Predicate asserting that a subset of k points forms the vertex set of a strictly convex k-gon. -/
def FormsConvexPolygon (S : Finset Point2D) (k : ℕ) : Prop :=
  ∃ (poly : Finset Point2D), poly ⊆ S ∧ poly.card = k ∧
    ∀ p ∈ poly, p ∉ convexHull ℝ (poly \ {p} : Set Point2D)

-- ============================================================================
-- Section 2: Esther Klein Base Theorem (ES(4) = 5)
-- ============================================================================

/-- Esther Klein's Theorem (1935):
    Any set of 5 points in general position in the plane contains a convex 4-gon. -/
theorem esther_klein_five_points (S : Finset Point2D)
    (h_card : S.card = 5)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S 4 := by
  sorry

-- ============================================================================
-- Section 3: General Erdős–Szekeres Theorem (1935)
-- ============================================================================

/-- The Erdős–Szekeres bound: ES(k) ≤ Nat.choose (2*k - 4) (k - 2) + 1. -/
def erdosSzekeresBound (k : ℕ) : ℕ :=
  Nat.choose (2 * k - 4) (k - 2) + 1

/-- Main Theorem: Erdős–Szekeres Convex Polygon Theorem (1935).
    Every set of at least ES(k) points in general position contains a convex k-gon. -/
theorem erdos_szekeres_convex_polygon (k : ℕ) (hk : 3 ≤ k)
    (S : Finset Point2D)
    (h_card : erdosSzekeresBound k ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S k := by
  sorry