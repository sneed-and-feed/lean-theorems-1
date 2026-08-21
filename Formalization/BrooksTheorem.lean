import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# Brooks' Theorem on Graph Colorings (1941)

This module formalizes **Brooks' Theorem** (R. L. Brooks, 1941), a foundational result
in graph theory and vertex coloring.

## Mathematical Statement

Let $G = (V, E)$ be a connected simple graph with maximum degree $\Delta(G) = \Delta \ge 1$.
Then the chromatic number $\chi(G)$ of $G$ satisfies:
$$\chi(G) \le \Delta$$
**unless** $G$ is one of two exceptional families:
1. $G$ is a complete graph $K_{\Delta + 1}$ (where $\chi(K_{\Delta + 1}) = \Delta + 1$).
2. $\Delta = 2$ and $G$ is an odd cycle $C_{2k+1}$ (where $\chi(C_{2k+1}) = 3 = \Delta + 1$).

For all other connected graphs (in particular, any graph with $\Delta \ge 3$ that is not a clique),
$G$ can be properly colored with $\Delta$ colors.

## Proof Techniques
1. **Greedy Coloring ($\chi(G) \le \Delta + 1$):**
   Ordering the vertices $v_1, \dots, v_n$ allows a greedy coloring where each vertex has at most $\Delta$
   previously colored neighbors, never exhausting $\Delta + 1$ available colors.
2. **2-Connected Reduction & Spanning DFS Trees:**
   When $G$ is 2-connected and not regular, one can find a vertex of degree $< \Delta$ and order the vertices
   towards it. When $G$ is $\Delta$-regular and 3-connected, one can find a pair of non-adjacent vertices
   $v_1, v_2$ with a common neighbor $v_n$ such that $G \setminus \{v_1, v_2\}$ is connected,
   giving $v_1$ and $v_2$ the same color and greedily coloring the rest.

## References
* Brooks, R. L. (1941). *On colouring the nodes of a network*. Mathematical Proceedings of the Cambridge Philosophical Society, 37(2), 194–197.
* Lovász, L. (1975). *Three short proofs in graph theory*. Journal of Combinatorial Theory, Series B, 19(3), 269–271.
* Diestel, R. (2017). *Graph Theory*. 5th edition, Springer.
* Freek Wiedijk. *Formalizing 100 Theorems*.
-/

namespace BrooksTheorem

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================================
-- Section 1: Maximum Degree and Proper Colorings
-- ============================================================================

/-- Maximum degree $\Delta(G)$ of a finite graph $G$. -/
def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun v => G.degree v)

/-- Predicate asserting that coloring `c` is a proper vertex coloring of `G`. -/
def IsProperColoring (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- Predicate asserting that graph `G` is `k`-colorable ($\chi(G) \le k$). -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProperColoring G c

-- ============================================================================
-- Section 2: Exceptional Graphs (Cliques and Odd Cycles)
-- ============================================================================

/-- A graph is complete ($K_n$) if every pair of distinct vertices is adjacent. -/
def IsCompleteGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v

/-- A graph is an odd cycle $C_{2k+1}$. -/
def IsOddCycle (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Odd (Fintype.card V) ∧ (∀ v : V, G.degree v = 2) ∧ G.Preconnected

-- ============================================================================
-- Section 3: Greedy Coloring Upper Bound
-- ============================================================================

/-- The classical greedy coloring theorem: any graph with maximum degree $\Delta$
    can be properly colored with $\Delta + 1$ colors. -/
theorem greedy_coloring_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsKColorable G (maxDegree G + 1) := by
  sorry

-- ============================================================================
-- Section 4: Main Brooks' Theorem (1941)
-- ============================================================================

/-- **Brooks' Theorem (1941):**
    If $G$ is a connected simple graph with maximum degree $\Delta \ge 1$,
    and $G$ is neither a complete graph $K_{\Delta+1}$ nor an odd cycle,
    then $G$ is $\Delta$-colorable ($\chi(G) \le \Delta$). -/
theorem brooks_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Preconnected)
    (h_deg_pos : 1 ≤ maxDegree G)
    (h_not_clique : ¬ (IsCompleteGraph G ∧ Fintype.card V = maxDegree G + 1))
    (h_not_odd_cycle : ¬ (maxDegree G = 2 ∧ IsOddCycle G)) :
    IsKColorable G (maxDegree G) := by
  sorry

end BrooksTheorem
