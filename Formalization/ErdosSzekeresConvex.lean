import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# The Happy Ending Theorem (Erdős–Szekeres Convex Polygon Theorem, 1935)

**The Happy Ending Theorem (Paul Erdős & George Szekeres, 1935)**
is one of the founding results of modern discrete and combinatorial geometry.

## Mathematical Statement
For every integer $k \ge 3$, there exists a smallest integer $ES(k)$ such that any set
of at least $ES(k)$ points in the Euclidean plane $\mathbb{R}^2$ in **general position**
(no three points collinear) contains the vertices of a convex $k$-gon.

Erdős and Szekeres proved the exact upper bound:
$$ES(k) \le \binom{2k - 4}{k - 2} + 1$$
and conjectured the exact value is $ES(k) = 2^{k - 2} + 1$:
- $k = 4 \implies ES(4) = 5$ (Esther Klein's original problem)
- $k = 5 \implies ES(5) = 9$ (Kalbfleisch et al. 1970 / Makai)
- $k = 6 \implies ES(6) = 17$ (Szekeres & Peters 2006)
- Asymptotics: $2^{k - o(k)} \le ES(k) \le 2^{k + o(k)}$ (Holmsen 2020, Suk 2017).

## Proof Technique (Cups and Caps / Ramsey Transition)
1. **Esther Klein Base Case ($k = 4$):** Among any 5 points in general position,
   either 4 form a convex quadrilateral directly, or the convex hull is a triangle containing
   2 interior points whose connecting line separates two of the triangle's vertices,
   forming a convex quad with the remaining vertices.
2. **Cup-Cap Lemma:** A sequence of points $(x_1, y_1), \dots, (x_m, y_m)$ sorted by $x$-coordinate
   forms an $a$-cup (convex downward) or a $b$-cap (convex upward).
   Any set of $\binom{a+b-4}{a-2} + 1$ points in general position contains an $a$-cup or a $b$-cap.
3. Setting $a = b = k$ yields a convex $k$-gon of size $\binom{2k-4}{k-2} + 1$.

## References
* Erdős, P., & Szekeres, G. (1935). *A combinatorial problem in geometry*. Compositio Mathematica, 2, 463–470.
* Klein, E. (1935). *Problem 1835*. Középiskolai Matematikai Lapok.
* Suk, A. (2017). *On the Erdős–Szekeres convex polygon problem*. Journal of the American Mathematical Society, 30(2), 347–353.
-/

-- ============================================================================
-- Section 1: General Position & Planar Convex Hulls
-- ============================================================================

/-- A point in the 2D Euclidean plane. -/
abbrev Point2D := ℝ × ℝ

/-- Signed area / orientation determinant of three points `p, q, r`. -/
def orientationDet (p q r : Point2D) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- Predicate asserting that a set of points is in general position (no three points collinear). -/
def InGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p q r, p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → p ≠ r →
    orientationDet p q r ≠ 0

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
-- Section 3: Cups, Caps, and the Erdős–Szekeres Bound
-- ============================================================================

/-- An ordered sequence of points forms an `a`-cup (convex downward). -/
def IsCup (pts : List Point2D) (a : ℕ) : Prop :=
  pts.length = a ∧
  ∀ i (hi : i + 2 < pts.length),
    orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) > 0

/-- An ordered sequence of points forms a `b`-cap (convex upward). -/
def IsCap (pts : List Point2D) (b : ℕ) : Prop :=
  pts.length = b ∧
  ∀ i (hi : i + 2 < pts.length),
    orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) < 0

/-- **Cup-Cap Lemma (Erdős–Szekeres 1935):**
    Any sequence of `Nat.choose (a + b - 4) (a - 2) + 1` points sorted by x-coordinate
    in general position contains an `a`-cup or a `b`-cap. -/
theorem cup_cap_lemma (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (S : Finset Point2D)
    (h_card : Nat.choose (a + b - 4) (a - 2) + 1 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    (∃ cup : List Point2D, IsCup cup a ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap b ∧ ∀ p ∈ cap, p ∈ S) := by
  sorry

/-- The Erdős–Szekeres bound: ES(k) ≤ Nat.choose (2*k - 4) (k - 2) + 1. -/
def erdosSzekeresBound (k : ℕ) : ℕ :=
  Nat.choose (2 * k - 4) (k - 2) + 1

/-- **Main Theorem: Erdős–Szekeres Convex Polygon Theorem (1935).**
    Every set of at least `erdosSzekeresBound k` points in general position contains a convex k-gon. -/
theorem erdos_szekeres_convex_polygon (k : ℕ) (hk : 3 ≤ k)
    (S : Finset Point2D)
    (h_card : erdosSzekeresBound k ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S k := by
  sorry

/-- The Erdős–Szekeres Exact Conjecture: ES(k) = 2^(k-2) + 1 for all k ≥ 3. -/
def ErdosSzekeresConjecture : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (S : Finset Point2D),
    2^(k - 2) + 1 ≤ S.card →
    InGeneralPosition S →
    FormsConvexPolygon S k