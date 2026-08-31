import Formalization.RuzsaFreiman.Basic
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise

set_option linter.unusedSectionVars false

/-!
# Ruzsa Distance and the Ruzsa Triangle Inequality

This module formalizes the **Ruzsa Distance** and the **Ruzsa Triangle Inequality** (Imre Z. Ruzsa, 1996),
which endows the space of finite subsets of an abelian group with a pseudometric structure.

## Mathematical Overview

For any two non-empty finite subsets $A, B$ of an additive abelian group $G$:
1. The **Ruzsa multiplicative ratio** is:
   $$\rho_R(A, B) = \frac{|A - B|}{\sqrt{|A| |B|}}$$
2. The **Ruzsa distance** is defined as:
   $$d_R(A, B) = \log \rho_R(A, B) = \log \frac{|A - B|}{\sqrt{|A| |B|}}$$

### Fundamental Properties

1. **Symmetry**: Since $|A - B| = |B - A|$, $d_R(A, B) = d_R(B, A)$.
2. **Translation Invariance**: For any $x, y \in G$, $d_R(A + x, B + y) = d_R(A, B)$.
3. **Non-negativity**: Since $|A - B| \ge \max(|A|, |B|) \ge \sqrt{|A| |B|}$, we have $\rho_R(A, B) \ge 1$ and $d_R(A, B) \ge 0$.
4. **Identity**: $d_R(A, A) = 0$ if and only if $A$ is a coset of a finite subgroup $H \le G$.
5. **Ruzsa Triangle Inequality**: For any finite subsets $A, B, C \subseteq G$:
   $$|B| \cdot |A - C| \le |A - B| \cdot |B - C|$$
   Taking logarithms, this translates into the standard triangle inequality for metric spaces:
   $$d_R(A, C) \le d_R(A, B) + d_R(B, C)$$

## Formalization Structure

- `ruzsaRatio`: The multiplicative ratio $\frac{|A - B|}{\sqrt{|A| |B|}}$.
- `ruzsaDistance`: The log-distance $d_R(A, B)$.
- `ruzsa_triangle_cardinality`: The fundamental cardinality bound $|B| \cdot |A - C| \le |A - B| \cdot |B - C|$.
- `ruzsa_triangle_inequality`: The logarithmic triangle inequality $d_R(A, C) \le d_R(A, B) + d_R(B, C)$.
- `diffset_le_sq_doubling`: The bound $|A - A| \le \frac{|A + A|^2}{|A|}$.

## References

- Ruzsa, I. Z. (1996). *Sums of finite sets*. Number Theory: New York Seminar, Springer, 281–293.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics.
-/

namespace RuzsaFreiman

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The Ruzsa multiplicative ratio $\rho_R(A, B) = \frac{|A - B|}{\sqrt{|A| |B|}}$. -/
noncomputable def ruzsaRatio (A B : Finset G) : ℝ :=
  (A - B).card / Real.sqrt ((A.card : ℝ) * (B.card : ℝ))

/-- The Ruzsa distance $d_R(A, B) = \log \frac{|A - B|}{\sqrt{|A| |B|}}$. -/
noncomputable def ruzsaDistance (A B : Finset G) : ℝ :=
  Real.log (ruzsaRatio A B)

/-- Difference set has same size under reflection: $|A - B| = |B - A|$. -/
theorem card_diffset_symm (A B : Finset G) :
    (A - B).card = (B - A).card := by
  rw [← Finset.card_neg, neg_sub]

/-- Symmetry of the Ruzsa distance: $d_R(A, B) = d_R(B, A)$. -/
theorem ruzsaDistance_symm (A B : Finset G) :
    ruzsaDistance A B = ruzsaDistance B A := by
  dsimp [ruzsaDistance, ruzsaRatio]
  rw [card_diffset_symm A B, mul_comm (A.card : ℝ)]

/--
**Ruzsa Triangle Inequality (Cardinality Form)**:
For any finite subsets $A, B, C$ in an additive group $G$:
$$|B| \cdot |A - C| \le |A - B| \cdot |B - C|$$
-/
theorem ruzsa_triangle_cardinality (A B C : Finset G) :
    B.card * (A - C).card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rw [mul_comm B.card, card_diffset_symm B C]
  exact h

/-- Strict positivity of the Ruzsa multiplicative ratio for non-empty sets. -/
theorem ruzsaRatio_pos {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    0 < ruzsaRatio A B := by
  have : (A - B).Nonempty := hA.sub hB
  dsimp [ruzsaRatio]
  positivity

/-- Multiplicative triangle inequality for the Ruzsa ratio. -/
theorem ruzsaRatio_mul_le {A B C : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    ruzsaRatio A C ≤ ruzsaRatio A B * ruzsaRatio B C := by
  dsimp [ruzsaRatio]
  have h_card : (B.card : ℝ) * (A - C).card ≤ (A - B).card * (B - C).card := by
    exact_mod_cast ruzsa_triangle_cardinality A B C
  have h_sqrt (X Y : Finset G) : Real.sqrt ((X.card : ℝ) * (Y.card : ℝ)) = Real.sqrt X.card * Real.sqrt Y.card :=
    Real.sqrt_mul (Nat.cast_nonneg _) _
  have hB_self : Real.sqrt B.card * Real.sqrt B.card = B.card := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have h_denom : Real.sqrt A.card * Real.sqrt B.card * (Real.sqrt B.card * Real.sqrt C.card) =
      (B.card : ℝ) * (Real.sqrt A.card * Real.sqrt C.card) := by
    linear_combination Real.sqrt A.card * Real.sqrt C.card * hB_self
  rw [div_mul_div_comm, h_sqrt A B, h_sqrt B C, h_sqrt A C, h_denom,
    ← mul_div_mul_left _ _ (ne_of_gt (by positivity : (0 : ℝ) < B.card))]
  exact div_le_div_of_nonneg_right h_card (by positivity)

/--
**Ruzsa Triangle Inequality (Metric Form)**:
For any non-empty finite subsets $A, B, C \subseteq G$:
$$d_R(A, C) \le d_R(A, B) + d_R(B, C)$$
-/
theorem ruzsa_triangle_inequality {A B C : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    ruzsaDistance A C ≤ ruzsaDistance A B + ruzsaDistance B C := by
  dsimp [ruzsaDistance]
  rw [← Real.log_mul (ne_of_gt (ruzsaRatio_pos hA hB)) (ne_of_gt (ruzsaRatio_pos hB hC))]
  exact Real.log_le_log (ruzsaRatio_pos hA hC) (ruzsaRatio_mul_le hA hB hC)

/--
**Difference Set Doubling Bound**:
For any non-empty finite set $A \subseteq G$,
$$|A - A| \le \frac{|A + A|^2}{|A|}$$
-/
theorem diffset_le_sq_doubling {A : Finset G} (hA : A.Nonempty) :
    (A - A).card ≤ (A + A).card ^ 2 / A.card := by
  have h := Finset.ruzsa_triangle_inequality_sub_add_add A A A
  rw [Nat.le_div_iff_mul_le hA.card_pos, sq]
  exact h

/--
**Iterated Difference Bound**:
For any non-empty finite set $A \subseteq G$ with $|A + A| \le K |A|$,
$|A - A| \le K^2 |A|$.
-/
theorem diffset_bound_of_doubling {A : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ((A - A).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
  have h_pos : (0 : ℝ) < A.card := by positivity
  have h_ineq : ((A - A).card : ℝ) * A.card ≤ ((A + A).card : ℝ) * (A + A).card := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add A A A
  exact (mul_le_mul_iff_of_pos_right h_pos).mp (by nlinarith)

end RuzsaFreiman
