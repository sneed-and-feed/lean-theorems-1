import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

open Finset

/-- A valid proper 3-coloring of the vertices of graph `G`. -/
def IsThreeColoring {V : Type*} (G : SimpleGraph V) (c : V → Fin 3) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- A guard set `S` covers every 3-clique / facial triangle in `G`. -/
def CoversTriangles {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj w u → (u ∈ S ∨ v ∈ S ∨ w ∈ S)

/-- **Fisk's Triangulation Guard Partition Lemma from 3-Colorings (1978)**:
Given a graph `G` on `n` vertices equipped with a valid proper 3-coloring `c` (such as a 3-colored
polygon triangulation), there exists a guard set `S` of size at most `⌊n / 3⌋` covering all facial triangles (3-cliques). -/
theorem art_gallery_theorem {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Fin 3) (hc : IsThreeColoring G c) :
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ CoversTriangles G S := sorry
