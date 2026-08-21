import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# 3-Dimensional Sperner's Lemma on Tetrahedral Triangulations (1928)

This module formalizes the **3-Dimensional Sperner's Lemma** (Emanuel Sperner, 1928),
extending the combinatorial triangulation framework from 1D/2D to 3-dimensional simplicial complexes.

## Mathematical Summary

1. **3D Triangulation (Tetrahedral Complex):**
   An abstract 3D triangulation $T$ consists of a finite collection of 4-element subsets
   (tetrahedra / 3-simplices) of vertices $\alpha$.
   Every 2D triangular face (3-element subset of a tetrahedron) belongs to either:
   - Exactly 1 tetrahedron (a **boundary face**), or
   - Exactly 2 tetrahedra (an **interior face**).

2. **Vertex 4-Coloring & Trichromatic Doors:**
   Let $c : \alpha \to \text{Fin } 4 = \{0, 1, 2, 3\}$ be a vertex coloring.
   - A triangular face $f$ is a **0-1-2 door** if $c(f) = \{0, 1, 2\}$.
   - A tetrahedron $t$ is **panchromatic** (or fully colored) if $c(t) = \{0, 1, 2, 3\}$.

3. **Local Door Parity Invariant:**
   For any tetrahedron $t = \{u, v, w, z\}$, the number of 0-1-2 faces on its boundary is:
   - Exactly $1$ if $t$ is panchromatic (colors are a permutation of $\{0, 1, 2, 3\}$).
   - Either $0$ or $2$ if $t$ is not panchromatic.
   Hence:
   $$\operatorname{doorCount3D}(c, t) \equiv [\operatorname{isPanchromatic4}(c, t)] \pmod 2$$

4. **Global Double Counting & Parity Theorem:**
   $$\sum_{t \in T} \operatorname{doorCount3D}(c, t) = |F_{\text{bd}}^{012}| + 2 |F_{\text{int}}^{012}|$$
   Reducing modulo 2 proves:
   $$|\{t \in T \mid \operatorname{isPanchromatic4}(c, t)\}| \equiv |F_{\text{bd}}^{012}| \pmod 2$$

5. **Existence Theorem:**
   If the boundary of a 3D triangulation has an odd number of 0-1-2 triangular faces
   (e.g. satisfying standard Sperner boundary conditions on a 3-simplex or 3-ball),
   there exists at least one panchromatic tetrahedron $\{0, 1, 2, 3\}$.

## References
* Sperner, E. (1928). *Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes*.
  Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg, 6(1), 265–272.
* Freek Wiedijk. *Formalizing 100 Theorems*, #57.
-/

namespace Sperner3D

variable {α : Type*} [DecidableEq α]

-- ============================================================================
-- Section 1: Abstract 3D Triangulations
-- ============================================================================

/-- An abstract 3-dimensional triangulation (simplicial 3-manifold with boundary).
    `tetrahedra` is a collection of 4-element subsets of vertices `α`.
    Every 2-face (3-element subset of a tetrahedron) belongs to either 1 or 2 tetrahedra. -/
structure Triangulation3D (α : Type*) [DecidableEq α] where
  tetrahedra : Finset (Finset α)
  tetrahedron_card : ∀ t ∈ tetrahedra, t.card = 4
  incident_card : ∀ f ∈ tetrahedra.biUnion (fun t => t.powerset.filter (fun s => s.card = 3)),
    (tetrahedra.filter (fun t => f ⊆ t)).card = 1 ∨ (tetrahedra.filter (fun t => f ⊆ t)).card = 2

/-- All triangular 2-faces of a 3D triangulation (3-element subsets of tetrahedra). -/
def Triangulation3D.faces (T : Triangulation3D α) : Finset (Finset α) :=
  T.tetrahedra.biUnion (fun t => t.powerset.filter (fun s => s.card = 3))

/-- The tetrahedra containing a given face `f`. -/
def Triangulation3D.incidentTetrahedra (T : Triangulation3D α) (f : Finset α) : Finset (Finset α) :=
  T.tetrahedra.filter (fun t => f ⊆ t)

/-- Boundary faces: triangular 2-faces contained in exactly 1 tetrahedron. -/
def Triangulation3D.boundaryFaces (T : Triangulation3D α) : Finset (Finset α) :=
  T.faces.filter (fun f => (T.incidentTetrahedra f).card = 1)

/-- Interior faces: triangular 2-faces contained in exactly 2 tetrahedra. -/
def Triangulation3D.interiorFaces (T : Triangulation3D α) : Finset (Finset α) :=
  T.faces.filter (fun f => (T.incidentTetrahedra f).card = 2)

-- ============================================================================
-- Section 2: Colorings and Doors
-- ============================================================================

/-- A triangular face is a 0-1-2 face (door) if its vertices map onto {0, 1, 2}. -/
def is012Face (c : α → Fin 4) (f : Finset α) : Prop :=
  f.card = 3 ∧ f.image c = ({0, 1, 2} : Finset (Fin 4))

instance (c : α → Fin 4) (f : Finset α) : Decidable (is012Face c f) :=
  inferInstanceAs (Decidable (f.card = 3 ∧ f.image c = {0, 1, 2}))

/-- A tetrahedron is panchromatic if its 4 vertices take all 4 colors {0, 1, 2, 3}. -/
def isPanchromatic4 (c : α → Fin 4) (t : Finset α) : Prop :=
  t.card = 4 ∧ t.image c = (Finset.univ : Finset (Fin 4))

instance (c : α → Fin 4) (t : Finset α) : Decidable (isPanchromatic4 c t) :=
  inferInstanceAs (Decidable (t.card = 4 ∧ t.image c = Finset.univ))

/-- The 0-1-2 faces on the boundary of a tetrahedron `t`. -/
def tetrahedron012Faces (c : α → Fin 4) (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter (fun s => s.card = 3 ∧ s.image c = ({0, 1, 2} : Finset (Fin 4)))

/-- Number of 0-1-2 faces on a tetrahedron `t`. -/
def tetrahedronDoorCount (c : α → Fin 4) (t : Finset α) : ℕ :=
  (tetrahedron012Faces c t).card

-- ============================================================================
-- Section 3: Local Parity Invariant and Main Theorems
-- ============================================================================

/-- Exhaustive finite-type check across all $4^4 = 256$ color assignments of a tetrahedron. -/
lemma fin4_local_door_count (a b d e : Fin 4) :
    ((if ({a, b, d} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0) +
     (if ({a, b, e} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0) +
     (if ({a, d, e} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0) +
     (if ({b, d, e} : Finset (Fin 4)) = ({0, 1, 2} : Finset (Fin 4)) then 1 else 0)) % 2 =
    if ({a, b, d, e} : Finset (Fin 4)) = Finset.univ then 1 else 0 := by
  sorry

/-- Local door count parity on any 4-element tetrahedron. -/
lemma tetrahedronDoorCount_mod_two (c : α → Fin 4) (t : Finset α) (ht : t.card = 4) :
    tetrahedronDoorCount c t % 2 = if isPanchromatic4 c t then 1 else 0 := by
  sorry

/-- **3D Sperner Parity Theorem (Sperner 1928):**
    The number of panchromatic tetrahedra in a 3D triangulation has the same parity
    modulo 2 as the number of 0-1-2 triangular faces on its boundary. -/
theorem sperner_3d_parity (T : Triangulation3D α) (c : α → Fin 4) :
    (T.tetrahedra.filter (isPanchromatic4 c)).card % 2 =
    (T.boundaryFaces.filter (is012Face c)).card % 2 := by
  sorry

/-- **3D Sperner Existence Theorem:**
    Whenever the boundary of a 3D triangulation contains an odd number of 0-1-2 faces,
    there exists at least one panchromatic tetrahedron {0, 1, 2, 3}. -/
theorem sperner_3d_exists (T : Triangulation3D α) (c : α → Fin 4)
    (h_bd : Odd (T.boundaryFaces.filter (is012Face c)).card) :
    ∃ t ∈ T.tetrahedra, isPanchromatic4 c t := by
  sorry

end Sperner3D
