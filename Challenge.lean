import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

namespace SchursTheorem

variable {α : Type*} [DecidableEq α]

/-- Ramsey number upper bound recurrence for monochromatic triangles in `r` colors:
    $R(0) = 2$, $R(r + 1) = (r + 1) \cdot R(r) + 1$. -/
def ramseyTriangleBound : ℕ → ℕ
  | 0 => 2
  | r + 1 => (r + 1) * ramseyTriangleBound r + 1

/-- A triple of distinct vertices forming a monochromatic triangle of color `k`. -/
def isMonoTriangle (c : α → α → Fin r) (S : Finset α) (u v w : α) (k : Fin r) : Prop :=
  u ∈ S ∧ v ∈ S ∧ w ∈ S ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
  c u v = k ∧ c u w = k ∧ c v w = k

/-- There exists a monochromatic triangle in `S` for edge-coloring `c`. -/
def hasMonoTriangle (c : α → α → Fin r) (S : Finset α) : Prop :=
  ∃ u v w k, isMonoTriangle c S u v w k

/-- **Multicolor Triangle Ramsey Theorem**:
Any symmetric edge-coloring with `r ≥ 1` colors of a complete graph with at least
`ramseyTriangleBound r` vertices contains a monochromatic triangle. -/
theorem ramsey_triangle :
    ∀ (r : ℕ) (_hr : 1 ≤ r) (S : Finset α) (c : α → α → Fin r),
      (∀ u v, c u v = c v u) →
      ramseyTriangleBound r ≤ S.card →
      hasMonoTriangle c S := sorry

/-- **Schur's Theorem on Sum-Free Partitions** (Issai Schur, 1916):
For any $r \ge 1$, every $r$-coloring $\chi$ of the integers $\{1, \dots, N\}$
(where $N = 	ext{ramseyTriangleBound } r$) contains a monochromatic solution to $x + y = z$:
$\exists c \in 	ext{Fin } r, \exists x, y, z \in \{1, \dots, N\}, \, \chi(x) = c \wedge \chi(y) = c \wedge \chi(z) = c \wedge x + y = z$. -/
theorem schurs_theorem (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    let N := ramseyTriangleBound r
    ∃ (c : Fin r) (x y z : ℕ),
      1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
      x ≤ N ∧ y ≤ N ∧ z ≤ N ∧
      x + y = z ∧
      χ x = c ∧ χ y = c ∧ χ z = c := sorry

end SchursTheorem
