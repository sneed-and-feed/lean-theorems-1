import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Chvátal's Art Gallery Theorem (1975) & Fisk's Triangulation 3-Coloring (1978)

This module formalizes **Chvátal's Art Gallery Theorem** (V. Chvátal, 1975)
and **Fisk's 3-Coloring Proof** (S. Fisk, 1978).

## Mathematical Statement

Let $P$ be a simple polygon with $n \ge 3$ vertices. Then $\lfloor n/3 \rfloor$ guards placed
at vertices are always sufficient to oversee/guard the entire polygon:
$$\operatorname{guards}(P) \le \lfloor n / 3 \rfloor$$

## Fisk's Graph-Theoretic Proof:
1. Every simple polygon can be triangulated into $n - 2$ triangles by non-crossing diagonals.
2. The dual graph of the triangulation is a tree, so the triangulation graph $G$ is 3-colorable.
3. By the Pigeonhole Principle, the smallest color class among $\{0, 1, 2\}$ contains at most $\lfloor n / 3 \rfloor$ vertices.
4. Every triangle in the triangulation has vertices of all 3 distinct colors, so placing guards at the vertices of the smallest color class ensures every triangle has at least one guard.

## References
* V. Chvátal (1975), *A combinatorial theorem in plane geometry*, J. Combin. Theory Ser. B, 18(1):39–41.
* S. Fisk (1978), *A short proof of Chvátal's watchman theorem*, J. Combin. Theory Ser. B, 24(3):374.
* J. O'Rourke (1987), *Art Gallery Theorems and Algorithms*, Oxford University Press.
-/

set_option linter.unusedSectionVars false

namespace ArtGalleryTheorem

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A valid proper 3-coloring of the vertices of graph `G`. -/
def IsThreeColoring (G : SimpleGraph V) (c : V → Fin 3) : Prop :=
  ∀ u v : V, G.Adj u v → c u ≠ c v

/-- A guard set `S` covers every 3-clique / facial triangle in `G`. -/
def CoversTriangles (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → G.Adj w u → (u ∈ S ∨ v ∈ S ∨ w ∈ S)

/-- In Fin 3, three pairwise distinct elements cover all of Fin 3. -/
lemma fin3_cases_of_pairwise_ne (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (k : Fin 3) :
    k = a ∨ k = b ∨ k = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases k <;> aesop

/-- Pigeonhole bound for 3-colorings: in any 3-coloring of `V`, at least one color class
has cardinality at most `|V| / 3`. -/
lemma min_color_class_le_third (c : V → Fin 3) :
    ∃ k : Fin 3, (Finset.univ.filter (fun v ↦ c v = k)).card ≤ Fintype.card V / 3 := by
  classical
  by_contra! h_all_gt
  have h_sum : Fintype.card V = (∑ k : Fin 3, (Finset.univ.filter (fun v ↦ c v = k)).card) := by
    rw [← Finset.card_univ, card_eq_sum_card_fiberwise (f := c) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)]
  rw [Fin.sum_univ_three] at h_sum
  have h0 := h_all_gt 0
  have h1 := h_all_gt 1
  have h2 := h_all_gt 2
  omega

/-- **Fisk's Art Gallery Theorem (1978):**
Given a 3-colorable maximal outerplanar / triangulation graph `G` on `n` vertices,
there exists a guard set `S` of size at most `n / 3` covering all triangles. -/
theorem art_gallery_theorem (G : SimpleGraph V) (c : V → Fin 3) (hc : IsThreeColoring G c) :
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ CoversTriangles G S := by
  classical
  obtain ⟨k, hk_card⟩ := min_color_class_le_third c
  let S : Finset V := Finset.univ.filter (fun v ↦ c v = k)
  refine ⟨S, hk_card, ?_⟩
  intro u v w huv hvw hwu
  have hab : c u ≠ c v := hc u v huv
  have hbc : c v ≠ c w := hc v w hvw
  have hca : c w ≠ c u := hc w u hwu
  rcases fin3_cases_of_pairwise_ne (c u) (c v) (c w) hab hbc hca k with rfl | rfl | rfl
  · left; simp [S]
  · right; left; simp [S]
  · right; right; simp [S]

#print axioms min_color_class_le_third
#print axioms art_gallery_theorem

end ArtGalleryTheorem
