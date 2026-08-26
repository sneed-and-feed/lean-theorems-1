import Formalization.ErdosSzekeresConvex.Orientation
import Formalization.ErdosSzekeresConvex.Sorting
import Formalization.ErdosSzekeresConvex.CupCap
import Formalization.ErdosSzekeresConvex.ConvexPolygon

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
(no three points collinear) with distinct $x$-coordinates contains the vertices of a convex $k$-gon.

Erdős and Szekeres proved the exact upper bound:
$$ES(k) \le \binom{2k - 4}{k - 2} + 1$$
and conjectured the exact value is $ES(k) = 2^{k - 2} + 1$:
- $k = 4 \implies ES(4) = 5$ (Esther Klein's original problem)
- $k = 5 \implies ES(5) = 9$ (Kalbfleisch et al. 1970 / Makai)
- $k = 6 \implies ES(6) = 17$ (Szekeres & Peters 2006)
- Asymptotics: $2^{k - o(k)} \le ES(k) \le 2^{k + o(k)}$ (Holmsen 2020, Suk 2017).

## Architecture & Modular Decomposition
This theorem is formalized across a modular 5-file architecture:
1. `Formalization.ErdosSzekeresConvex.Orientation`: Foundations of planar orientations, general
   position, determinant symmetries, and strict halfspace separation lemmas for convex hulls.
2. `Formalization.ErdosSzekeresConvex.Sorting`: 2D plane rotations, lexicographical order on $\mathbb{R}^2$,
   and the sorting theorem for finite sets with distinct $x$-coordinates.
3. `Formalization.ErdosSzekeresConvex.CupCap`: Formal definition of $a$-cups and $b$-caps, extension lemmas,
   the binomial coefficient split recurrence, and the full Erdős–Szekeres cup-cap theorem.
4. `Formalization.ErdosSzekeresConvex.ConvexPolygon`: Transitivity of orientations, 4-point determinant identities,
   and strict convex polygon formation from cups and caps.
5. `Formalization.ErdosSzekeresConvex`: Top-level master interface presenting the main theorems and corollaries.

## References
* Erdős, P., & Szekeres, G. (1935). *A combinatorial problem in geometry*. Compositio Mathematica, 2, 463–470.
* Klein, E. (1935). *Problem 1835*. Középiskolai Matematikai Lapok.
* Suk, A. (2017). *On the Erdős–Szekeres convex polygon problem*. Journal of the American Mathematical Society, 30(2), 347–353.
-/

/-- The Erdős–Szekeres upper bound: ES(k) ≤ Nat.choose (2*k - 4) (k - 2) + 1. -/
def erdosSzekeresBound (k : ℕ) : ℕ :=
  Nat.choose (2 * k - 4) (k - 2) + 1

/-- **Main Theorem: Erdős–Szekeres Convex Polygon Theorem (1935).**
    Every set of at least `erdosSzekeresBound k` points in general position with distinct x-coordinates
    contains the vertices of a strictly convex k-gon (`FormsConvexPolygon S k`). -/
theorem erdos_szekeres_convex_polygon (k : ℕ) (hk : 3 ≤ k)
    (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : erdosSzekeresBound k ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S k := by
  rcases cup_cap_lemma k k hk hk S h_dist (by rwa [show k + k = 2 * k by omega]) h_gen with ⟨C, hC, hC_sub⟩ | ⟨C, hC, hC_sub⟩
  · exact formsConvexPolygon_of_isCup S C k hk hC hC_sub
  · exact formsConvexPolygon_of_isCap S C k hk hC hC_sub

/-- For k = 3, every set of at least 3 points in general position with distinct x-coordinates
    contains a convex triangle. Exact evaluation: ES(3) = 3. -/
theorem erdos_szekeres_triangle (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : 3 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S 3 :=
  erdos_szekeres_convex_polygon 3 (by omega) S h_dist h_card h_gen

/-- For k = 4, every set of at least 7 points in general position with distinct x-coordinates
    contains a convex quadrilateral (general upper bound `ES(4) ≤ 7`). -/
theorem erdos_szekeres_four_points (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : 7 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S 4 :=
  erdos_szekeres_convex_polygon 4 (by omega) S h_dist h_card h_gen

/-- **Esther Klein's Theorem (1935 / Klein's Problem 1835):**
    Every set of at least `erdosSzekeresBound 4` (= 7) points in general position with distinct x-coordinates
    contains a convex quadrilateral (exact value `ES(4) = 5`, combinatorial upper bound `ES(4) ≤ 7`). -/
theorem esther_klein_theorem (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : erdosSzekeresBound 4 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S 4 :=
  erdos_szekeres_convex_polygon 4 (by omega) S h_dist h_card h_gen

/-- The Erdős–Szekeres Exact Conjecture: ES(k) = 2^(k-2) + 1 for all k ≥ 3.
    Proven for k = 3 (ES=3), k = 4 (ES=5, Esther Klein), k = 5 (ES=9, Kalbfleisch et al.),
    and k = 6 (ES=17, Szekeres–Peters 2006). Open for k ≥ 7. -/
def ErdosSzekeresConjecture : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (S : Finset Point2D),
    HasDistinctX S →
    2^(k - 2) + 1 ≤ S.card →
    InGeneralPosition S →
    FormsConvexPolygon S k
