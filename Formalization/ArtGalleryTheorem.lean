import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Fisk's Triangulation Guard Partition Lemma from 3-Colorings (1978)

This module formalizes **Fisk's Triangulation Guard Partition Lemma** (S. Fisk, 1978),
the combinatorial partition and pigeonhole core of Steve Fisk's proof of Chvátal's
Art Gallery Theorem (V. Chvátal, 1975).

## Mathematical Overview

Given a simple polygon with $n \ge 3$ vertices:
1. Every polygon admits a triangulation whose dual tree structure implies the graph is 3-colorable.
2. Given any proper 3-coloring $c : V \to \{0, 1, 2\}$, the Pigeonhole Principle guarantees
   at least one color class $V_k = c^{-1}(k)$ has size:
   $$|V_k| \le \lfloor n / 3 \rfloor$$
3. Since every facial triangle (3-clique) receives 3 distinct colors, $V_k$ intersects every triangle,
   forming a valid guard set of size $\le \lfloor n / 3 \rfloor$.

This module formalizes step 2–3 as the Guard Partition Lemma from a 3-coloring, treating triangulation
and 3-colorability as external preconditions.

## References
* V. Chvátal (1975), *A combinatorial theorem in plane geometry*, J. Combin. Theory Ser. B, 18(1):39–41.
* S. Fisk (1978), *A short proof of Chvátal's watchman theorem*, J. Combin. Theory Ser. B, 24(3):374.
* J. O'Rourke (1987), *Art Gallery Theorems and Algorithms*, Oxford University Press.
-/


namespace ArtGalleryTheorem

open Finset

variable {V : Type*} [Fintype V]

/-- A valid proper 3-coloring of the vertices of graph `G`. -/
def IsThreeColoring (G : SimpleGraph V) (c : V → Fin 3) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- A guard set `S` covers every 3-clique / facial triangle in `G`. -/
def CoversTriangles (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj w u → (u ∈ S ∨ v ∈ S ∨ w ∈ S)

/-- In Fin 3, three pairwise distinct elements cover all of Fin 3. -/
lemma fin3_cases_of_pairwise_ne (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (k : Fin 3) :
    k = a ∨ k = b ∨ k = c := by
  revert a b c k; decide

/-- Generalized pigeonhole bound for $k$-colorings: for any coloring $c : V \to \text{Fin } k$ with $k \ge 1$,
    at least one color class has cardinality at most $|V| / k$. -/
lemma min_color_class_le_k {k : ℕ} (hk : 0 < k) (c : V → Fin k) :
    ∃ col : Fin k, (univ.filter (fun v ↦ c v = col)).card ≤ Fintype.card V / k := by
  classical
  by_contra! h
  have H : Fintype.card V = ∑ col : Fin k, (univ.filter (fun v ↦ c v = col)).card := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := c) (t := univ) (by simp)]
  have h2 : k * (Fintype.card V / k + 1) ≤ Fintype.card V := by
    calc k * (Fintype.card V / k + 1) = ∑ _col : Fin k, (Fintype.card V / k + 1) := by simp
      _ ≤ ∑ col : Fin k, (univ.filter (fun v ↦ c v = col)).card := sum_le_sum (fun i _ ↦ h i)
      _ = Fintype.card V := H.symm
  have h3 := Nat.lt_mul_div_succ (Fintype.card V) hk
  omega

/-- **Fisk's Triangulation Guard Partition Lemma (1978):**
Given a graph `G` on `n` vertices equipped with a valid proper 3-coloring `c` (such as a 3-colored
polygon triangulation), there exists a guard set `S` of size at most `n / 3` covering all triangles (3-cliques). -/
theorem art_gallery_theorem [DecidableEq V] (G : SimpleGraph V) (c : V → Fin 3) (hc : IsThreeColoring G c) :
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ CoversTriangles G S := by
  classical
  obtain ⟨k, hk_card⟩ := min_color_class_le_k (by decide) c
  use univ.filter (fun v ↦ c v = k), hk_card
  intro u v w huv hvw hwu
  rcases fin3_cases_of_pairwise_ne (c u) (c v) (c w) (hc u v huv) (hc v w hvw) (hc w u hwu) k with rfl | rfl | rfl <;> simp

/-- Fisk's Guard Partition Lemma formulated using Mathlib's native `SimpleGraph.Coloring` type. -/
theorem art_gallery_theorem_coloring [DecidableEq V] (G : SimpleGraph V) (c : G.Coloring (Fin 3)) :
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ CoversTriangles G S :=
  art_gallery_theorem G c (fun _ _ huv ↦ c.valid huv)

end ArtGalleryTheorem

export ArtGalleryTheorem (IsThreeColoring CoversTriangles art_gallery_theorem)
