import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.Order

open Polynomial

/-- Number of sign variations in a real sequence (ignoring zeros). -/
noncomputable def sign_variations : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
    if x = 0 then sign_variations (y :: rest)
    else if y = 0 then sign_variations (x :: rest)
    else (if x * y < 0 then 1 else 0) + sign_variations (y :: rest)

/-- Sign variations of the non-zero coefficients of a polynomial p(X). -/
noncomputable def poly_sign_variations (p : Polynomial ℝ) : ℕ :=
  sign_variations (List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)))

/-- Total number of positive real roots of p(X) counted with algebraic multiplicity. -/
noncomputable def pos_roots_count (p : Polynomial ℝ) : ℕ :=
  (p.roots.filter (· > (0 : ℝ))).card

/-- **Descartes's Rule of Signs (1637, Wiedijk #73)**:
The number of positive real roots of a non-zero real polynomial $p(X)$ (counted with multiplicity)
is bounded above by the number of sign variations in its coefficient sequence, and differs from it
by an even non-negative integer. -/
theorem descartes_rule_of_signs (p : Polynomial ℝ) (hp : p ≠ 0) :
    pos_roots_count p ≤ poly_sign_variations p ∧
    Even (poly_sign_variations p - pos_roots_count p) := sorry
