import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (politician) in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

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

/-- **The Friendship Windmill Structure Theorem (Erdős–Rényi–Sós 1966)**:
Every finite graph satisfying the friendship property is a windmill graph $Wd(k, 2)$ consisting of $k$ triangles sharing a universal vertex. -/
theorem friendship_windmill (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) : ∃ (w : V) (k : ℕ), IsWindmillGraph G w k := sorry
