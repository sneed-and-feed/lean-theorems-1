import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# The Friendship Theorem (Erdős–Rényi–Sós, 1966)

This module provides the formalization stub for the **Friendship Theorem**
(P. Erdős, A. Rényi, V. T. Sós, 1966).

## Mathematical Statement
Let $G = (V, E)$ be a finite simple graph such that every pair of distinct vertices has
*exactly one* common neighbor:
$$\forall u \ne v \in V, \quad |N(u) \cap N(v)| = 1$$

Then there exists a universal vertex $w \in V$ connected to all other vertices
($\deg(w) = |V| - 1$), and the graph $G$ consists of a set of triangles sharing the single
universal vertex $w$ (a "windmill graph" or "friendship graph" $Wd(k, 2)$).

## References
* P. Erdős, A. Rényi, V. T. Sós (1966), *On a problem of graph theory*, Studia Sci. Math. Hungar., 1:215–235.
* H. S. Wilf (1971), *The friendship theorem*, in *Combinatorial Mathematics and its Applications*, Academic Press.
-/

namespace FriendshipTheorem

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (or "politician") in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

/-- **The Friendship Theorem (Erdős–Rényi–Sós 1966):**
Any finite simple graph in which every pair of distinct vertices shares exactly one
common neighbor has a universal vertex. -/
theorem friendship_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (h_card : 3 ≤ Fintype.card V) :
    ∃ w : V, IsUniversalVertex G w := by
  sorry

end FriendshipTheorem
