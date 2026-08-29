import Formalization.RuzsaFreiman.Basic
import Formalization.RuzsaFreiman.RuzsaDistance
import Formalization.RuzsaFreiman.PlunneckeRuzsa
import Formalization.RuzsaFreiman.GAP

/-!
# Ruzsa Calculus, Plünnecke–Ruzsa Bounds & Generalized Arithmetic Progressions

This module aggregates the complete additive combinatorics package:
1. `Basic.lean`: Sumsets, difference sets, doubling constants $\sigma(A)$, difference constants $\delta(A)$.
2. `RuzsaDistance.lean`: Ruzsa pseudometric $d_R(A, B)$, Ruzsa triangle inequality $|B| |A - C| \le |A - B| |B - C|$.
3. `PlunneckeRuzsa.lean`: Plünnecke–Ruzsa bounds $|k B - \ell B| \le K^{k+\ell} |A|$ and Petridis minimal magnification.
4. `GAP.lean`: Multi-dimensional Generalized Arithmetic Progressions (GAPs), volume bounds $|P| \le \prod N_i$, and Freiman homomorphism properties.

## References
- Freiman, G. A. (1966). *Foundations of a Structural Theory of Set Addition*.
- Ruzsa, I. Z. (1994, 1996). *Sums of finite sets* / *Generalized arithmetical progressions and sumsets*.
- Petridis, G. (2012). *New proofs of Plünnecke-type estimates for sumsets*.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge University Press.
-/
