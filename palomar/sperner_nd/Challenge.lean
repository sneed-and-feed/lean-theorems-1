import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Ring.Parity

open Finset

namespace SpernerND

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- An abstract $n$-dimensional pseudomanifold with boundary on vertex type `α`.
    `topSimplices` is a finite family of $(n+1)$-element subsets of `α`.
    Every $n$-element facet (an $n$-element subset of a top simplex) is contained
    in either exactly 1 top simplex (boundary) or exactly 2 top simplices (interior). -/
structure PseudomanifoldND (α : Type*) [DecidableEq α] (n : ℕ) where
  topSimplices : Finset (Finset α)
  top_card : ∀ t ∈ topSimplices, t.card = n + 1
  incident_card : ∀ f ∈ topSimplices.biUnion (fun t => t.powerset.filter (fun s => s.card = n)),
    (topSimplices.filter (fun t => f ⊆ t)).card = 1 ∨ (topSimplices.filter (fun t => f ⊆ t)).card = 2

/-- All $n$-element facets ($(n-1)$-simplices) of an $n$-dimensional pseudomanifold. -/
def PseudomanifoldND.facets (M : PseudomanifoldND α n) : Finset (Finset α) :=
  M.topSimplices.biUnion (fun t => t.powerset.filter (fun s => s.card = n))

/-- The top simplices containing a given facet `f`. -/
def PseudomanifoldND.incidentSimplices (M : PseudomanifoldND α n) (f : Finset α) : Finset (Finset α) :=
  M.topSimplices.filter (fun t => f ⊆ t)

/-- Boundary facets: $n$-element facets contained in exactly 1 top simplex. -/
def PseudomanifoldND.boundaryFacets (M : PseudomanifoldND α n) : Finset (Finset α) :=
  M.facets.filter (fun f => (M.incidentSimplices f).card = 1)

/-- Interior facets: $n$-element facets contained in exactly 2 top simplices. -/
def PseudomanifoldND.interiorFacets (M : PseudomanifoldND α n) : Finset (Finset α) :=
  M.facets.filter (fun f => (M.incidentSimplices f).card = 2)

/-- An $n$-element facet `f` is a door if its vertices map bijectively onto the first $n$ colors
    $\{0, 1, \dots, n-1\} = \text{univ} \setminus \{\text{Fin.last } n\}$. -/
def isDoor (c : α → Fin (n + 1)) (f : Finset α) : Prop :=
  f.card = n ∧ f.image c = (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n)

instance instDecidableIsDoor (c : α → Fin (n + 1)) (f : Finset α) : Decidable (isDoor c f) :=
  inferInstanceAs (Decidable (f.card = n ∧ f.image c = Finset.univ.erase (Fin.last n)))

/-- An $(n+1)$-element top simplex `t` is panchromatic (fully labeled) if its vertices
    take all $n+1$ colors $\{0, 1, \dots, n\}$. -/
def isPanchromatic (c : α → Fin (n + 1)) (t : Finset α) : Prop :=
  t.card = n + 1 ∧ t.image c = (Finset.univ : Finset (Fin (n + 1)))

instance instDecidableIsPanchromatic (c : α → Fin (n + 1)) (t : Finset α) : Decidable (isPanchromatic c t) :=
  inferInstanceAs (Decidable (t.card = n + 1 ∧ t.image c = Finset.univ))

/-- **General n-Dimensional Sperner Parity Theorem (Sperner, 1928):**
    The number of panchromatic $(n+1)$-simplices in any $n$-dimensional pseudomanifold
    with boundary has the same parity modulo 2 as the number of $(n-1)$-doors on its boundary. -/
theorem sperner_nd_parity (M : PseudomanifoldND α n) (c : α → Fin (n + 1)) :
    (M.topSimplices.filter (isPanchromatic c)).card % 2 =
    (M.boundaryFacets.filter (isDoor c)).card % 2 := sorry

/-- **General n-Dimensional Sperner's Lemma (Parity Form):**
    If the boundary contains an odd number of $(n-1)$-doors, the number of panchromatic
    $(n+1)$-simplices is odd. -/
theorem sperner_nd_odd (M : PseudomanifoldND α n) (c : α → Fin (n + 1))
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    Odd (M.topSimplices.filter (isPanchromatic c)).card := sorry

/-- **General n-Dimensional Sperner Existence Theorem:**
    Whenever the boundary of an $n$-dimensional pseudomanifold contains an odd number of
    $(n-1)$-doors, there exists at least one panchromatic $(n+1)$-simplex (taking all $n+1$ colors). -/
theorem sperner_nd_exists (M : PseudomanifoldND α n) (c : α → Fin (n + 1))
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    ∃ t ∈ M.topSimplices, isPanchromatic c t := sorry

end SpernerND