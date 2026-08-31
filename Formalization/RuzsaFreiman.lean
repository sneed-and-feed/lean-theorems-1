import Formalization.RuzsaFreiman.Basic
import Formalization.RuzsaFreiman.RuzsaDistance
import Formalization.RuzsaFreiman.PlunneckeRuzsa
import Formalization.RuzsaFreiman.FreimanTheorem

/-!
# Ruzsa Calculus & Freiman's Structural Theorem

This module aggregates the complete additive combinatorics package:
1. `Basic.lean`: Sumsets, difference sets, doubling constants $\sigma(A)$, difference constants $\delta(A)$.
2. `RuzsaDistance.lean`: Ruzsa pseudometric $d_R(A, B)$, Ruzsa triangle inequality $|B| |A - C| \le |A - B| |B - C|$.
3. `PlunneckeRuzsa.lean`: Plünnecke–Ruzsa bounds $|k B - \ell B| \le K^{k+\ell} |A|$ and Petridis minimal magnification.
4. `FreimanTheorem.lean`: Multi-dimensional Generalized Arithmetic Progressions (GAPs), Freiman's structural theorem in $\mathbb{Z}$, Bogolyubov's lemma, and the Polynomial Freiman–Ruzsa theorem in $\mathbb{F}_2^n$.

## References
- Freiman, G. A. (1966). *Foundations of a Structural Theory of Set Addition*.
- Ruzsa, I. Z. (1994, 1996). *Generalized arithmetical progressions and sumsets*.
- Petridis, G. (2012). *New proofs of Plünnecke-type estimates for sumsets*.
- Gowers, W. T., Green, B., Manners, F., & Tao, T. (2023). *On a conjecture of Marton*.
-/
