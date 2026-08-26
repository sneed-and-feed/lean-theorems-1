import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Fintype.Card

open SimpleGraph

/-- **Ore's Theorem (1960)**:
A simple graph $G$ on $n \ge 3$ vertices in which $\deg(u) + \deg(v) \ge n$ for every pair of
distinct non-adjacent vertices $u, v$ contains a Hamiltonian cycle. -/
theorem ore_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hore : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := sorry

/-- **Dirac's Theorem (1952)**:
A simple graph $G$ on $n \ge 3$ vertices with minimum degree $\delta(G) \ge \lceil n / 2 \rceil$
contains a Hamiltonian cycle. -/
theorem dirac_hamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 3 ≤ Fintype.card V)
    (hdirac : ∀ v : V, (Fintype.card V + 1) / 2 ≤ G.degree v) :
    ∃ (v : V) (p : G.Walk v v), p.IsHamiltonianCycle := sorry
