import Formalization.TverbergsTheorem.Basis
import Formalization.TverbergsTheorem.Sarkaria
import Formalization.TverbergsTheorem.Dim1
import Formalization.TverbergsTheorem.Colorful

/-!
# Tverberg's Theorem: Reductions, 1D Theorem, and Colorful 1D Theorem

Tverberg's theorem (H. Tverberg, 1966) is a foundational result in discrete and combinatorial
geometry generalizing Radon's lemma ($r = 2$). The formalization is organized into four modular
subcomponents:

1. `Formalization.TverbergsTheorem.Basis`: Auxiliary zero-sum basis vectors, affine coordinate lifting,
   and the formal predicate `IsTverbergPartition` along with superset extension.
2. `Formalization.TverbergsTheorem.Sarkaria`: Sarkaria's algebraic reduction via tensor lifting,
   Colorful Carathéodory zero-sum reduction for pairs, Radon's theorem ($r = 2$), and Tverberg's
   theorem for $r \le 2$.
3. `Formalization.TverbergsTheorem.Dim1`: Complete 1-dimensional Tverberg theorem for arbitrary $r \ge 1$
   via sorted order embeddings, median selection, and symmetric pairing.
4. `Formalization.TverbergsTheorem.Colorful`: 1-dimensional Colorful Tverberg theorem for arbitrary $r \ge 1$
   (Bárány–Larman–Pach 1992 / $d = 1$) via sorted colorful pairing.

## Mathematical Statement

Let $d \ge 1$ and $r \ge 1$. Any set $S \subset \mathbb{R}^d$ of cardinality:
$$N = (r - 1)(d + 1) + 1$$
can be partitioned into $r$ pairwise disjoint subsets $A_1, \dots, A_r$ whose convex hulls
share a common point of intersection:
$$\bigcap_{i=1}^r \operatorname{conv}(A_i) \ne \emptyset$$

## Main Exported Declarations

* `auxVec`: Standard auxiliary basis vectors in $\mathbb{R}^m$ with zero sum.
* `liftAffine`: Lifted point in affine space $\mathbb{R}^{d+1}$ ($x \mapsto (x, 1)$).
* `IsTverbergPartition`: Predicate defining a valid Tverberg partition of a point set.
* `IsTverbergPartition.extend_superset`: Extension of a Tverberg partition to a superset.
* `sarkariaLift`: Sarkaria tensor lifting of a point with color index into $\mathbb{R}^{(d+1) \times m}$.
* `sarkaria_tverberg`: Sarkaria-Bárány algebraic reduction from zero-sum tensor combinations.
* `radons_theorem`: Classical Radon lemma ($r = 2$).
* `tverbergs_theorem`: Tverberg's theorem for $r \le 2$ (Radon for $r = 2$, trivial for $r = 1$).
* `mem_convexHull_pair_1d`: A 1D point between two endpoints lies in their convex hull.
* `tverberg_1d`: Exact 1D Tverberg theorem for $|S| = 2r - 1$.
* `tverberg_1d_of_card_ge`: Monotone 1D Tverberg theorem for $|S| \ge 2r - 1$.
* `colorful_tverberg_1d`: 1-dimensional Colorful Tverberg theorem for 2 color classes of size $r$.

## References

* H. Tverberg (1966), *A generalization of Radon's theorem*, J. London Math. Soc. 41:123–128,
  Theorem 1. https://doi.org/10.1112/jlms/s1-41.1.123
* K. S. Sarkaria (1992), *Tverberg's theorem via number of roots of polynomial systems*,
  Israel J. Math. 79:317–320.
* I. Bárány, D. G. Larman, and J. Pach (1992), *Radon-partition property in topological affine spaces*,
  Amer. Math. Monthly 99(5):422–431.
* W. Mulzer and D. Werner (2013), *Approximating Tverberg points in linear time for any fixed
  dimension*, Discrete Comput. Geom. 50:520–535, §2.2, Lemma 2.3 and Theorem 2.4.
* J. Matoušek (2002), *Lectures on Discrete Geometry*, GTM 212, Springer, Chapter 8.
-/

set_option linter.deprecated false

namespace TverbergsTheorem

-- Check all main declarations in the namespace
#check auxVec
#check liftAffine
#check IsTverbergPartition
#check IsTverbergPartition.extend_superset
#check sarkariaLift
#check sarkaria_tverberg
#check radons_theorem
#check tverbergs_theorem
#check mem_convexHull_pair_1d
#check tverberg_1d
#check tverberg_1d_of_card_ge
#check colorful_tverberg_1d

end TverbergsTheorem

#print axioms TverbergsTheorem.radons_theorem
#print axioms TverbergsTheorem.tverbergs_theorem
#print axioms TverbergsTheorem.sarkaria_tverberg
#print axioms TverbergsTheorem.mem_convexHull_pair_1d
#print axioms TverbergsTheorem.tverberg_1d
#print axioms TverbergsTheorem.IsTverbergPartition.extend_superset
#print axioms TverbergsTheorem.tverberg_1d_of_card_ge
#print axioms TverbergsTheorem.colorful_tverberg_1d
