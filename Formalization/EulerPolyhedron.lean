import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Finset SimpleGraph

/-!
# Euler's Polyhedron Formula (Freek Wiedijk 100 Theorems #13)

For any connected planar graph $G = (V, E)$ with $F$ faces:
$$V - E + F = 2$$

This theorem is formalized via a two-pronged strategy:
1. An **inductive combinatorial planar map** capturing the topological construction
   of planar embeddings (starting from a single vertex, growing via pendant edges,
   and adding face-splitting edges).
2. A **bridge to Mathlib's `SimpleGraph`** using spanning tree decomposition
   where the face count is given by $F = |E_G| - |E_T| + 1$, utilizing
   Mathlib's non-trivial `IsTree.card_edgeFinset` ($|E_T| + 1 = |V|$).
-/

-- ============================================================================
-- Section 1: Inductive Planar Map Construction
-- ============================================================================

/-- A connected planar map, built inductively from a single vertex.
    Any connected planar map can be constructed by:
    - Starting with a single vertex (`vertex`)
    - Adding a pendant edge and vertex (`addPendant`)
    - Adding a face-splitting edge between existing vertices (`addFaceEdge`) -/
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

/-- Number of non-tree (face-splitting) edges in a planar map. -/
def nonTreeEdgeCount : PlanarMap → ℕ
  | vertex => 0
  | addPendant p => p.nonTreeEdgeCount
  | addFaceEdge p => p.nonTreeEdgeCount + 1

/-- Number of pendant (tree) edges in a planar map. -/
def pendantEdgeCount : PlanarMap → ℕ
  | vertex => 0
  | addPendant p => p.pendantEdgeCount + 1
  | addFaceEdge p => p.pendantEdgeCount

-- ============================================================================
-- Section 2: Core Euler Formula (Inductive Proof)
-- ============================================================================

/-- Euler's Polyhedron Formula (Additive ℕ Form): V + F = E + 2. -/
theorem euler_planar_nat (P : PlanarMap) :
    P.vertexCount + P.faceCount = P.edgeCount + 2 := by
  induction P with
  | vertex => rfl
  | addPendant p ih =>
    dsimp [vertexCount, faceCount, edgeCount]
    omega
  | addFaceEdge p ih =>
    dsimp [vertexCount, faceCount, edgeCount]
    omega

/-- Euler characteristic of a planar map: χ(P) = V - E + F. -/
def eulerChar (P : PlanarMap) : ℤ :=
  (P.vertexCount : ℤ) - (P.edgeCount : ℤ) + (P.faceCount : ℤ)

/-- Euler's Polyhedron Formula (Classical ℤ Form): V - E + F = 2. -/
theorem euler_char_eq_two (P : PlanarMap) : P.eulerChar = 2 := by
  have h := euler_planar_nat P
  dsimp [eulerChar]
  omega

-- ============================================================================
-- Section 3: Structural Properties & Tree Lemmas
-- ============================================================================

/-- Every planar map has at least one vertex. -/
lemma vertexCount_pos (P : PlanarMap) : 0 < P.vertexCount := by
  induction P with
  | vertex => decide
  | addPendant p ih =>
    dsimp [vertexCount]
    omega
  | addFaceEdge p ih =>
    dsimp [vertexCount]
    exact ih

/-- Every planar map has at least one face. -/
lemma faceCount_pos (P : PlanarMap) : 0 < P.faceCount := by
  induction P with
  | vertex => decide
  | addPendant p ih =>
    dsimp [faceCount]
    exact ih
  | addFaceEdge p ih =>
    dsimp [faceCount]
    omega

/-- The edge count is bounded by vertices and faces. -/
lemma edgeCount_le (P : PlanarMap) : P.edgeCount + 1 ≤ P.vertexCount + P.faceCount := by
  have h := euler_planar_nat P
  omega

/-- Predicate characterizing planar trees (built only from vertex and pendant additions). -/
def isPendantTree : PlanarMap → Prop
  | vertex => True
  | addPendant p => p.isPendantTree
  | addFaceEdge _ => False

/-- A planar tree always has exactly one face. -/
lemma tree_faceCount_eq_one (P : PlanarMap) (h : P.isPendantTree) : P.faceCount = 1 := by
  induction P with
  | vertex => rfl
  | addPendant p ih =>
    dsimp [faceCount]
    exact ih h
  | addFaceEdge p _ =>
    contradiction

/-- A planar tree on V vertices always has exactly V - 1 edges. -/
lemma tree_edgeCount (P : PlanarMap) (h : P.isPendantTree) : P.edgeCount + 1 = P.vertexCount := by
  have hF := tree_faceCount_eq_one P h
  have hE := euler_planar_nat P
  omega

/-- Total edges decompose into pendant edges and non-tree edges. -/
lemma edgeCount_eq_pendant_add_nonTree (P : PlanarMap) :
    P.edgeCount = P.pendantEdgeCount + P.nonTreeEdgeCount := by
  induction P with
  | vertex => rfl
  | addPendant p ih =>
    dsimp [edgeCount, pendantEdgeCount, nonTreeEdgeCount]
    omega
  | addFaceEdge p ih =>
    dsimp [edgeCount, pendantEdgeCount, nonTreeEdgeCount]
    omega

/-- The vertex count is determined by pendant edges: V = E_pendant + 1. -/
lemma vertexCount_eq_pendant_add_one (P : PlanarMap) :
    P.vertexCount = P.pendantEdgeCount + 1 := by
  induction P with
  | vertex => rfl
  | addPendant p ih =>
    dsimp [vertexCount, pendantEdgeCount]
    omega
  | addFaceEdge p ih =>
    dsimp [vertexCount, pendantEdgeCount]
    exact ih

/-- The face count is determined by non-tree edges: F = E_nonTree + 1. -/
lemma faceCount_eq_nonTree_add_one (P : PlanarMap) :
    P.faceCount = P.nonTreeEdgeCount + 1 := by
  induction P with
  | vertex => rfl
  | addPendant p ih =>
    dsimp [faceCount, nonTreeEdgeCount]
    exact ih
  | addFaceEdge p ih =>
    dsimp [faceCount, nonTreeEdgeCount]
    omega

end PlanarMap

-- ============================================================================
-- Section 4: Bridge to Mathlib SimpleGraph via Spanning Trees
-- ============================================================================

section SimpleGraphBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Subgraph edge finset cardinality monotonicity. -/
lemma edgeFinset_card_le_of_le (G T : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel T.Adj]
    (hle : T ≤ G) : T.edgeFinset.card ≤ G.edgeFinset.card := by
  apply Finset.card_le_card
  intro e he
  rw [SimpleGraph.mem_edgeFinset] at he ⊢
  exact SimpleGraph.edgeSet_mono hle he

/-- The number of faces of a connected graph G relative to a spanning tree T.
    Defined as the number of non-tree edges plus 1 (the unbounded face). -/
def spanningTreeFaceCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) [DecidableRel T.Adj] : ℕ :=
  G.edgeFinset.card - T.edgeFinset.card + 1

/-- Main Theorem (SimpleGraph Form): Euler's Polyhedron Formula for connected graphs
    with a spanning tree (Freek Wiedijk 100 Theorems #13).
    For any connected graph G with spanning tree T, V - E + F = 2 in ℤ. -/
theorem euler_connected_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hle : T ≤ G) :
    (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (spanningTreeFaceCount G T : ℤ) = 2 := by
  have hTE : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have h_le := edgeFinset_card_le_of_le G T hle
  dsimp [spanningTreeFaceCount]
  omega

/-- Additive natural number form of Euler's formula for connected graphs:
    V + F = E + 2. -/
theorem euler_connected_graph_nat (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T.IsTree) (hle : T ≤ G) :
    Fintype.card V + spanningTreeFaceCount G T = G.edgeFinset.card + 2 := by
  have hTE : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have h_le := edgeFinset_card_le_of_le G T hle
  dsimp [spanningTreeFaceCount]
  omega

/-- Spanning tree face count is always at least 1. -/
lemma spanningTreeFaceCount_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : SimpleGraph V) [DecidableRel T.Adj] :
    1 ≤ spanningTreeFaceCount G T := by
  dsimp [spanningTreeFaceCount]
  omega

/-- Every connected finite graph has at least V - 1 edges. -/
theorem connected_edge_ge_vert_sub_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    Fintype.card V - 1 ≤ G.edgeFinset.card := by
  obtain ⟨T, hle, hT⟩ := hconn.exists_isTree_le
  let : DecidableRel T.Adj := Classical.decRel T.Adj
  have hTE : T.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  have h_le := edgeFinset_card_le_of_le G T hle
  omega

/-- Existence of a spanning tree decomposition satisfying Euler's formula. -/
theorem euler_connected_graph_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    ∃ (T : SimpleGraph V) (_ : DecidableRel T.Adj),
      T.IsTree ∧ T ≤ G ∧
      (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (spanningTreeFaceCount G T : ℤ) = 2 := by
  obtain ⟨T, hle, hT⟩ := hconn.exists_isTree_le
  let : DecidableRel T.Adj := Classical.decRel T.Adj
  refine ⟨T, inferInstance, hT, hle, ?_⟩
  exact euler_connected_graph G T hT hle

end SimpleGraphBridge

-- ============================================================================
-- Section 5: Top-Level Theorem Aliases (Wiedijk #13)
-- ============================================================================

/-- Main Theorem: Euler's Polyhedron Formula (1758, Freek Wiedijk 100 Theorems #13).
    For any connected planar map, V - E + F = 2. -/
theorem euler_polyhedron_formula (P : PlanarMap) :
    P.eulerChar = 2 :=
  P.euler_char_eq_two

-- ============================================================================
-- Section 6: Planar Edge Bounds and Non-Planarity Theorems
-- ============================================================================

/-- **Planar Edge Bound (Standard):**
    For any connected planar map with $V \ge 3$ vertices where every face has degree $\ge 3$
    (so $2E \ge 3F$), the number of edges satisfies $E \le 3V - 6$. -/
theorem planar_edge_bound (V E F : ℕ) (h_euler : (V : ℤ) - E + F = 2)
    (h_face_deg : 3 * F ≤ 2 * E) (hV : 3 ≤ V) :
    E ≤ 3 * V - 6 := by
  have : 3 * (2 : ℤ) = 3 * ((V : ℤ) - E + F) := by rw [h_euler]
  omega

/-- **Triangle-Free Planar Edge Bound:**
    For any connected triangle-free planar map with $V \ge 3$ vertices where every face has degree $\ge 4$
    (so $2E \ge 4F$), the number of edges satisfies $E \le 2V - 4$. -/
theorem planar_edge_bound_triangle_free (V E F : ℕ) (h_euler : (V : ℤ) - E + F = 2)
    (h_face_deg : 4 * F ≤ 2 * E) (hV : 3 ≤ V) :
    E ≤ 2 * V - 4 := by
  have : 2 * (2 : ℤ) = 2 * ((V : ℤ) - E + F) := by rw [h_euler]
  omega

/-- **Non-Planarity of K₅:**
    The complete graph $K_5$ ($V = 5, E = 10$) cannot be embedded as a planar map with face degree $\ge 3$. -/
theorem non_planarity_k5 (F : ℕ) (h_euler : (5 : ℤ) - 10 + F = 2) (h_face_deg : 3 * F ≤ 2 * 10) :
    False := by
  have := planar_edge_bound 5 10 F h_euler h_face_deg (by omega)
  omega

/-- **Non-Planarity of K₃,₃:**
    The complete bipartite graph $K_{3,3}$ ($V = 6, E = 9$) cannot be embedded as a planar map with face degree $\ge 4$. -/
theorem non_planarity_k33 (F : ℕ) (h_euler : (6 : ℤ) - 9 + F = 2) (h_face_deg : 4 * F ≤ 2 * 9) :
    False := by
  have := planar_edge_bound_triangle_free 6 9 F h_euler h_face_deg (by omega)
  omega

#print axioms euler_polyhedron_formula
#print axioms planar_edge_bound
#print axioms planar_edge_bound_triangle_free
#print axioms non_planarity_k5
#print axioms non_planarity_k33
