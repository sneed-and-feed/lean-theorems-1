import Formalization.SchursTheorem.Basic
import Formalization.SchursTheorem.Group
import Formalization.SchursTheorem.Quantitative
import Formalization.SchursTheorem.Rado

/-!
# Schur's Theorem: Algebraic, Quantitative & Linear Systems Suite

This is the top-level integration module for the upgraded **Schur's Theorem** formalization suite
in additive combinatorics and algebraic Ramsey theory.

## Theoretical Overview & Historical Context

Originating in Issai Schur's 1916 investigation of Fermat's Last Theorem over finite fields
(*Über die Kongruenz $x^m + y^m \equiv z^m \pmod p$*), Schur's Theorem established that any
finite coloring of the positive integers contains a monochromatic solution to $x + y = z$.

This formalization suite extends Schur's classical result into a comprehensive, multi-dimensional
research-grade package encompassing three core modern directions:

1. **Foundational & Classical Integer Formulations (`Formalization.SchursTheorem.Basic`)**:
   - `SchursTheorem.ramseyTriangleBound`: Explicit recursive upper bound $B_r = (r+1)B(r)+1$ on $R_r(3)$.
   - `SchursTheorem.ramsey_triangle`: Monochromatic triangle existence in symmetric complete graph colorings.
   - `SchursTheorem.schurs_theorem`: Monochromatic $x + y = z$ in $\{1, \dots, B_r\}$.
   - `SchursTheorem.schurs_theorem_color_classes`: Non-sum-free color classes.
   - `SchursTheorem.schurs_theorem_partition`: Partition regularity under finite coverings.

2. **Group-Theoretic & Algebraic Extensions (`Formalization.SchursTheorem.Group`)**:
   - `SchursTheorem.group_schurs_theorem`: Multiplicative Schur theorem in arbitrary groups $(G, \cdot)$
     via difference/Cayley graph colorings ($x \cdot y = z$ for $|S| \ge B_r$).
   - `SchursTheorem.addCommGroup_schurs_theorem`: Additive Schur theorem in arbitrary abelian groups $(A, +)$ ($|S| \ge B_r$).
   - `SchursTheorem.finite_group_partition_regular`: Partition regularity of $G \setminus \{1\}$ with non-identity witnesses ($x, y, z \ne 1$).
   - `SchursTheorem.finite_group_color_classes_not_product_free`: Finite group product-free partitions.
   - `SchursTheorem.finite_addCommGroup_partition_regular`: Partition regularity of $A \setminus \{0\}$ with non-zero witnesses ($x, y, z \ne 0$).

3. **Quantitative Supersaturation & Counting (`Formalization.SchursTheorem.Quantitative`)**:
   - `SchursTheorem.monoSchurTriples`: Finset of monochromatic Schur triples in $\{1, \dots, N\}$.
   - `SchursTheorem.card_monoSchurTriples_one`: Exact quadratic formula $\frac{(N-1)N}{2} = \frac{1}{2}N^2 - \frac{1}{2}N$ for $r = 1$.
   - `SchursTheorem.card_monoTriangles_ge_k`: Disjoint block embedding proving at least $k$ graph triangles.
   - `SchursTheorem.supersaturation_bound`: Quantitative disjoint-block double-counting lower bound $k \le N \cdot |\text{monoSchurTriples } \chi N|$.
   - `SchursTheorem.card_monoSchurTriples_eq_sum_color`: Color class decomposition identity.

4. **Single-Equation Rado Partition Regularity (`Formalization.SchursTheorem.Rado`)**:
   - `SchursTheorem.rado_zero_sum_partition_regular`: Constant-solution zero-sum corollary to Rado's theorem ($\sum c_i = 0$).
   - `SchursTheorem.schur_is_rado_regular`: Schur's equation $(1, 1, -1)$ partition regularity over $\mathbb{N}^+$.
   - `SchursTheorem.schur_interval_bound`: Explicit finite interval cutoff $B_r = \text{ramseyTriangleBound } r$.
   - `SchursTheorem.ap3_is_rado_regular`: 3-term arithmetic progression $(1, -2, 1)$ zero-sum regularity.
   - `SchursTheorem.add4_is_rado_regular`: 4-variable additive balance equation $(1, 1, -1, -1)$.

## Bound Fidelity (Anti-Pattern Q Compliance)
All docstrings and theorem types explicitly distinguish the recursive upper bound $B_r = \text{ramseyTriangleBound } r$
from the exact canonical extremal invariants $S(r)$ and $R_r(3)$.

## References
* Schur, I. (1916). *Über die Kongruenz $x^m + y^m \equiv z^m \pmod p$*. Jahresbericht der DMV, 25:114–117.
* Ramsey, F. P. (1930). *On a Problem in Formal Logic*. Proc. London Math. Soc., 30:264–286.
* Rado, R. (1933). *Studien zur Kombinatorik*. Mathematische Zeitschrift, 36:424–480.
* Graham, R. L., Rothschild, B. L., Spencer, J. H. (1990). *Ramsey Theory*. John Wiley & Sons.
-/