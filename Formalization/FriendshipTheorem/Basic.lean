import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Basic Definitions and Lemmas for Friendship Graphs

This module provides the fundamental definitions and structural lemmas for graphs
satisfying the **Friendship Property** (every pair of distinct vertices has exactly
one common neighbor).

## Main Definitions
* `FriendshipTheorem.HasFriendshipProperty`: Predicate stating that any two distinct
  vertices in $G$ share a unique common neighbor.
* `FriendshipTheorem.IsUniversalVertex`: Predicate stating that a vertex $w$ is connected
  to every other vertex in $G$.
* `FriendshipTheorem.commonNeighbor`: The unique common neighbor of two distinct vertices.

## Main Lemmas
* `commonNeighbor_mem_inter`: The common neighbor belongs to the intersection of neighborhoods.
* `inter_eq_singleton_commonNeighbor`: The intersection of neighborhoods is the singleton `{commonNeighbor}`.
* `commonNeighbor_adj_left`, `commonNeighbor_adj_right`: Adjacency relations with the common neighbor.
* `commonNeighbor_symm`: Symmetry of the common neighbor function.
* `commonNeighbor_eq_of_mem`: Any vertex in the neighborhood intersection equals the common neighbor.
* `commonNeighbor_ne_left`, `commonNeighbor_ne_right`: The common neighbor is distinct from both endpoints.
-/

namespace FriendshipTheorem

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The friendship property: every pair of distinct vertices has exactly one common neighbor. -/
def HasFriendshipProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1

/-- A universal vertex (or "politician") in `G` that is adjacent to all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (w : V) : Prop :=
  ∀ v : V, v ≠ w → G.Adj w v

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The unique common neighbor of two distinct vertices in a friendship graph. -/
noncomputable def commonNeighbor (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) : V :=
  Finset.card_eq_one.mp (h_friend u v huv) |>.choose

lemma commonNeighbor_mem_inter (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv ∈ G.neighborFinset u ∩ G.neighborFinset v :=
  (Finset.card_eq_one.mp (h_friend u v huv)).choose_spec.symm ▸ Finset.mem_singleton_self _

lemma inter_eq_singleton_commonNeighbor (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    G.neighborFinset u ∩ G.neighborFinset v = {commonNeighbor h_friend huv} :=
  Finset.card_eq_one.mp (h_friend u v huv) |>.choose_spec

lemma commonNeighbor_adj_left (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    G.Adj u (commonNeighbor h_friend huv) :=
  (G.mem_neighborFinset u _).mp (Finset.mem_inter.mp (commonNeighbor_mem_inter h_friend huv)).1

lemma commonNeighbor_adj_right (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    G.Adj v (commonNeighbor h_friend huv) :=
  (G.mem_neighborFinset v _).mp (Finset.mem_inter.mp (commonNeighbor_mem_inter h_friend huv)).2

lemma commonNeighbor_eq_of_mem (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v)
    {w : V} (hw : w ∈ G.neighborFinset u ∩ G.neighborFinset v) :
    w = commonNeighbor h_friend huv :=
  Finset.mem_singleton.mp (inter_eq_singleton_commonNeighbor h_friend huv ▸ hw)

lemma commonNeighbor_symm (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv = commonNeighbor h_friend huv.symm :=
  commonNeighbor_eq_of_mem h_friend huv.symm <|
    Finset.mem_inter.mpr (Finset.mem_inter.mp (commonNeighbor_mem_inter h_friend huv)).symm

lemma commonNeighbor_ne_left (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv ≠ u :=
  (commonNeighbor_adj_left h_friend huv).ne.symm

lemma commonNeighbor_ne_right (h_friend : HasFriendshipProperty G) {u v : V} (huv : u ≠ v) :
    commonNeighbor h_friend huv ≠ v :=
  (commonNeighbor_adj_right h_friend huv).ne.symm

end FriendshipTheorem
