import Formalization.FriendshipTheorem.Basic
import Formalization.FriendshipTheorem.Politician
import Formalization.FriendshipTheorem.Walks
import Formalization.FriendshipTheorem.Windmill

/-!
# The Friendship Theorem (Erdős–Rényi–Sós, 1966)

This module formalizes the **Friendship Theorem** (P. Erdős, A. Rényi, V. T. Sós, 1966).

## Mathematical Statement
Let $G = (V, E)$ be a finite simple graph such that every pair of distinct vertices has
*exactly one* common neighbor:
$$\forall u \ne v \in V, \quad |N(u) \cap N(v)| = 1$$

Then there exists a universal vertex $w \in V$ connected to all other vertices
($\deg(w) = |V| - 1$), and the graph $G$ consists of a set of triangles sharing the single
universal vertex $w$ (a "windmill graph" or "friendship graph" $Wd(k, 2)$).

## Modular Architecture
- `Formalization.FriendshipTheorem.Basic`: Fundamental predicates (`HasFriendshipProperty`,
  `IsUniversalVertex`), unique common neighbor operation, and basic neighborhood properties.
- `Formalization.FriendshipTheorem.Politician`: Non-adjacent degree equality, universal vertex
  from degree disparity, even degree parity via neighborhood involution, and the order formula.
- `Formalization.FriendshipTheorem.Walks`: Walk counts, matrix powers mod $p$, $\mathbb{Z}/p\mathbb{Z}$
  group action on closed walks, and elimination of $k$-regular graphs for $k \ge 3$.
- `Formalization.FriendshipTheorem.Windmill`: The 2-regular base case ($K_3$) and windmill graph structure.

## References
* P. Erdős, A. Rényi, V. T. Sós (1966), *On a problem of graph theory*, Studia Sci. Math. Hungar., 1:215–235.
* H. S. Wilf (1971), *The friendship theorem*, in *Combinatorial Mathematics and its Applications*, Academic Press.
-/

namespace FriendshipTheorem

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The Friendship Theorem (Erdős–Rényi–Sós 1966):**
Any finite simple graph in which every pair of distinct vertices shares exactly one
common neighbor has a universal vertex. -/
theorem friendship_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_friend : HasFriendshipProperty G) (h_card : 3 ≤ Fintype.card V) :
    ∃ w : V, IsUniversalVertex G w := by
  by_cases h_reg_all : ∀ a b : V, G.degree a = G.degree b
  · obtain ⟨u₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let k := G.degree u₀
    have h_reg (v : V) : G.degree v = k := h_reg_all v u₀
    rcases le_or_gt 3 k with (hk3 | hk_lt3)
    · exact (no_regular_friendship_graph_ge_three h_friend k hk3 h_reg h_card).elim
    · obtain ⟨c, hc⟩ : Even k := even_degree_of_friendship h_friend u₀
      have hk_eq_2 : k = 2 := by
        obtain ⟨v, hv⟩ : ∃ v, v ≠ u₀ := by
          have : 1 < Fintype.card V := by omega
          exact Fintype.exists_ne_of_one_lt_card this u₀
        have h_inter := h_friend u₀ v hv.symm
        have h_deg : k ≠ 0 := by
          intro h_zero
          have h_card_zero : (G.neighborFinset u₀).card = 0 := h_zero
          rw [Finset.card_eq_zero] at h_card_zero
          rw [h_card_zero, Finset.empty_inter, Finset.card_empty] at h_inter
          omega
        omega
      have h_reg2 (v : V) : G.degree v = 2 := by rw [h_reg v, hk_eq_2]
      exact two_regular_has_universal h_friend h_reg2 h_card
  · push Not at h_reg_all
    exact exists_universal_of_exists_degree_ne h_friend h_reg_all

end FriendshipTheorem
