import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

namespace DeBruijnErdos

variable {α : Type*} [DecidableEq α]

/-- A finite linear space consists of a set of points `P : Finset α` and a set of lines
`L : Finset (Finset α)` satisfying:
1. Every line is a subset of `P`.
2. Every line contains at least 2 points.
3. Any two distinct points lie on a unique line.
4. Non-collinearity: no single line contains all points `P`.
5. Non-degeneracy: there are at least 3 points. -/
structure LinearSpace (P : Finset α) (L : Finset (Finset α)) : Prop where
  line_subset : ∀ l ∈ L, l ⊆ P
  line_card_ge_two : ∀ l ∈ L, 2 ≤ l.card
  unique_line : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ∃! l ∈ L, u ∈ l ∧ v ∈ l
  non_collinear : ∀ l ∈ L, ¬ P ⊆ l
  three_le_card : 3 ≤ P.card

/-- The lines of a near-pencil configuration on point set `P` with apex `p₀ ∈ P`:
one long line `P \ {p₀}` containing all other points, and `|P| - 1` lines of size 2
connecting `p₀` to each other point. -/
def nearPencilLines (P : Finset α) (p₀ : α) : Finset (Finset α) :=
  insert (P.erase p₀) ((P.erase p₀).image (fun q => {p₀, q}))

/-- **The De Bruijn–Erdős Theorem on Incidence Geometry (1948)**:
In any finite non-collinear linear space with at least 3 points, the number of lines
is at least the number of points: `|P| ≤ |L|`. -/
theorem de_bruijn_erdos {P : Finset α} {L : Finset (Finset α)}
    (h : LinearSpace P L) : P.card ≤ L.card := sorry

/-- **Tightness of the De Bruijn–Erdős Theorem**:
For any finite set of points `P` with `|P| ≥ 3` and any point `p₀ ∈ P`,
the near-pencil linear space on `P` with apex `p₀` achieves equality: `|L| = |P|`. -/
theorem de_bruijn_erdos_tight (P : Finset α) (p₀ : α) (hp₀ : p₀ ∈ P) (hcard : 3 ≤ P.card) :
    LinearSpace P (nearPencilLines P p₀) ∧ (nearPencilLines P p₀).card = P.card := sorry

end DeBruijnErdos
