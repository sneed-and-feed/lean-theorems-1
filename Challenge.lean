import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace FriendshipTheorem

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
    ∃ w : V, IsUniversalVertex G w := sorry

end FriendshipTheorem
