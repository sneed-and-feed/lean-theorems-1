import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open Finset SimpleGraph

/-- A connected planar map, built inductively from a single vertex. -/
inductive PlanarMap : Type where
  | vertex : PlanarMap
  | addPendant : PlanarMap → PlanarMap
  | addFaceEdge : PlanarMap → PlanarMap
deriving DecidableEq, Repr

namespace PlanarMap

/-- Number of vertices in a planar map. -/
def vertexCount : PlanarMap → ℕ
  | vertex => 1
  | addPendant p => p.vertexCount + 1
  | addFaceEdge p => p.vertexCount

/-- Number of edges in a planar map. -/
def edgeCount : PlanarMap → ℕ
  | vertex => 0
  | addPendant p => p.edgeCount + 1
  | addFaceEdge p => p.edgeCount + 1

/-- Number of faces in a planar map (including the unbounded exterior face). -/
def faceCount : PlanarMap → ℕ
  | vertex => 1
  | addPendant p => p.faceCount
  | addFaceEdge p => p.faceCount + 1

/-- Euler characteristic of a planar map: χ(P) = V - E + F. -/
def eulerChar (P : PlanarMap) : ℤ :=
  (P.vertexCount : ℤ) - (P.edgeCount : ℤ) + (P.faceCount : ℤ)

end PlanarMap

/-- **Euler's Polyhedron Formula (1758, Wiedijk #13)**:
For any inductively generated connected planar map, $V - E + F = 2$. -/
theorem euler_polyhedron_formula (P : PlanarMap) : P.eulerChar = 2 := sorry

section SimpleGraphBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of faces of a connected graph G relative to a spanning tree T.
    Defined as the number of non-tree edges plus 1 (the unbounded face). -/
def spanningTreeFaceCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) [DecidableRel T.Adj] : ℕ :=
  G.edgeFinset.card - T.edgeFinset.card + 1

/-- **Euler's Formula for Connected Graphs via Spanning Trees**:
For any finite connected graph $G$ with spanning tree $T$, $V - E + F = 2$ in $\mathbb{Z}$. -/
theorem euler_connected_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hle : T ≤ G) :
    (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (spanningTreeFaceCount G T : ℤ) = 2 := sorry

end SimpleGraphBridge
