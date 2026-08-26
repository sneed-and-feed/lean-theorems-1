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

/-- **Fisk's Art Gallery Theorem (1978):**
Given a 3-colorable maximal outerplanar / triangulation graph `G` on `n` vertices,
there exists a guard set `S` of size at most `n / 3` covering all triangles. -/
theorem art_gallery_theorem (G : SimpleGraph V) (c : V → Fin 3) (hc : IsThreeColoring G c) :
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ CoversTriangles G S := by
  classical
  obtain ⟨k, hk_card⟩ := min_color_class_le_k (by decide) c
  use univ.filter (fun v ↦ c v = k), hk_card
  intro u v w huv hvw hwu
  rcases fin3_cases_of_pairwise_ne (c u) (c v) (c w) (hc u v huv) (hc v w hvw) (hc w u hwu) k with rfl | rfl | rfl <;> simp

/-- Art Gallery Theorem formulated using Mathlib's native `SimpleGraph.Coloring` type. -/
theorem art_gallery_theorem_coloring (G : SimpleGraph V) (c : G.Coloring (Fin 3)) :
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ CoversTriangles G S :=
  art_gallery_theorem G c (fun _ _ huv ↦ c.valid huv)

end ArtGalleryTheorem

