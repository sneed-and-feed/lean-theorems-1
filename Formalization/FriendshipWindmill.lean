import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# The Friendship Theorem: Windmill Classification & Structure (1966)

This module formalizes the **complete structural classification** of friendship graphs
as **windmill graphs** $Wd(k, 2)$ (P. Erdős, A. Rényi, V. T. Sós, 1966).

## Mathematical Statement

Let $G = (V, E)$ be a finite simple graph where every pair of distinct vertices
shares exactly one common neighbor:
$$\forall u \ne v \in V, \quad |N(u) \cap N(v)| = 1$$

Building upon the existence of a universal vertex (politician) $w \in V$
satisfying $\deg(w) = |V| - 1$:
1. **Odd Cardinality:** The number of vertices $|V|$ is always odd: $|V| = 2k + 1$ for some $k \ge 1$.
2. **1-Factor Structure:** The induced subgraph on $V \setminus \{w\}$ is $1$-regular (a perfect matching
   of $k$ disjoint edges $\{u_1, v_1\}, \dots, \{u_k, v_k\}$).
3. **Windmill Isomorphism:** The graph $G$ consists of $k$ triangles sharing only the central apex vertex $w$
   (a "windmill graph" or "friendship graph" $Wd(k, 2) = K_1 \vee k K_2$).
4. **Edge Count:** The total number of edges in $G$ is exactly $3k = \frac{3(|V| - 1)}{2}$.

## References
* Erdős, P., Rényi, A., & Sós, V. T. (1966). *On a problem of graph theory*. Studia Sci. Math. Hungar., 1:215–235.
* Wilf, H. S. (1971). *The friendship theorem*. Combinatorial Mathematics and Its Applications, Academic Press.
* Bondy, J. A., & Murty, U. S. R. (2008). *Graph Theory*. Graduate Texts in Mathematics 244, Springer.
-/

namespace FriendshipWindmill

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (politician) in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

-- ============================================================================
-- Section 1: Politician Properties & Induced Matching
-- ============================================================================

/-- In a graph with the friendship property, the politician vertex `w` is adjacent to all other vertices. -/
theorem politician_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V)
    (h_univ : IsUniversalVertex G w) :
    G.degree w = Fintype.card V - 1 := by
  sorry

/-- The induced subgraph on the non-politician vertices `V \ {w}` is 1-regular (every vertex has degree 1). -/
theorem induced_non_politician_degree_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V)
    (h_univ : IsUniversalVertex G w) (v : V) (hv : v ≠ w) :
    ((G.neighborFinset v).erase w).card = 1 := by
  sorry

-- ============================================================================
-- Section 2: Odd Cardinality and Windmill Classification
-- ============================================================================

/-- **Friendship Graph Odd Vertex Count:**
    The number of vertices in any friendship graph is odd ($|V| = 2k + 1$). -/
theorem friendship_graph_odd_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) :
    Odd (Fintype.card V) := by
  sorry

/-- Predicate defining a windmill graph $Wd(k, 2)$: a central vertex `w` connected to
    `k` vertex-disjoint triangles. -/
def IsWindmillGraph (G : SimpleGraph V) (w : V) (k : ℕ) : Prop :=
  IsUniversalVertex G w ∧
  Fintype.card V = 2 * k + 1 ∧
  ∃ (matching : Finset (Finset V)),
    matching.card = k ∧
    (∀ e ∈ matching, e.card = 2 ∧ w ∉ e) ∧
    (∀ e₁ ∈ matching, ∀ e₂ ∈ matching, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
    (∀ u v, u ≠ w → v ≠ w → (G.Adj u v ↔ {u, v} ∈ matching))

/-- **Windmill Classification Theorem (Erdős–Rényi–Sós 1966):**
    Every graph satisfying the friendship property is a windmill graph $Wd(k, 2)$. -/
theorem friendship_is_windmill (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) :
    ∃ (w : V) (k : ℕ), IsWindmillGraph G w k := by
  sorry

/-- The total edge count of any friendship graph on $2k + 1$ vertices is exactly $3k$. -/
theorem friendship_edge_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (w : V) (k : ℕ)
    (h_wind : IsWindmillGraph G w k) :
    G.edgeFinset.card = 3 * k := by
  sorry

end FriendshipWindmill
