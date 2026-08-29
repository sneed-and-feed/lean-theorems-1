import Formalization.KonigMatching.Basic
import Formalization.KonigMatching.Defect
import Formalization.KonigMatching.Duality

/-!
# Kőnig–Egerváry Duality Theorem

This module formalizes the **Kőnig–Egerváry Theorem** (Dénes Kőnig, 1931; Jenő Egerváry, 1931),
a cornerstone of combinatorial optimization and structural graph theory establishing strong
min-max duality between matchings and vertex covers in bipartite graphs.

## Submodules
- `Formalization.KonigMatching.Basic`: Basic definitions (matching, vertex cover, independent set), invariants ($\nu, \tau, \alpha$), and Weak Duality ($\nu(G) \le \tau(G)$).
- `Formalization.KonigMatching.Defect`: Maximal defect subsets, augmented neighborhood family, Hall's defect condition, and matching extraction.
- `Formalization.KonigMatching.Duality`: Strong Duality ($\nu(G) = \tau(G)$), Gallai's identity ($\alpha(G) + \tau(G) = |V|$), and Kőnig independence formula ($\alpha(G) + \nu(G) = |V|$).

## Main Theorems
- `SimpleGraph.matching_card_le_vertexCover_card`: $|M| \le |C|$ for any matching $M$ and cover $C$.
- `SimpleGraph.weak_duality`: $\nu(G) \le \tau(G)$ for any finite simple graph.
- `SimpleGraph.konig_duality_le`: $\tau(G) \le \nu(G)$ for bipartite ($2$-colorable) graphs.
- `SimpleGraph.konig_duality`: $\nu(G) = \tau(G)$ for bipartite ($2$-colorable) graphs.
- `SimpleGraph.gallai_independence_vertex_cover`: $\alpha(G) + \tau(G) = |V|$ for any finite simple graph.
- `SimpleGraph.konig_independence_matching`: $\alpha(G) + \nu(G) = |V|$ for bipartite graphs.

## References
- Kőnig, D. (1931). *Gráfok és mátrixok*. Matematikai és Fizikai Lapok, 38, 116–119.
- Egerváry, J. (1931). *Matrixok kombinatorius tulajdonságairól*. Matematikai és Fizikai Lapok, 38, 16–28.
- Gallai, T. (1959). *Über extreme Punkt- und Kantenmengen*. Ann. Univ. Sci. Budapest, Eötvös Sect. Math., 2, 133–138.
- Schrijver, A. (2003). *Combinatorial Optimization: Polyhedra and Efficiency*. Springer.
-/
