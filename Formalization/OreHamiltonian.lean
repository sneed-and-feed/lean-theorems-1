import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Fintype.Card

open SimpleGraph

/-- Ore's Theorem (1960): A simple graph on n ≥ 3 vertices with deg(u) + deg(v) ≥ n
    for all non-adjacent u ≠ v has a Hamiltonian cycle. -/
theorem ore_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := by
  sorry

/-- Corollary: Dirac's Theorem (1952). -/
theorem dirac_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdirac : ∀ v : V, (Fintype.card V + 1) / 2 ≤ G.degree v) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := by
  sorry
