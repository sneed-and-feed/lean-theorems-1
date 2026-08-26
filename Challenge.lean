import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

open Finset

/-- A complete bipartite decomposition of K_n is given by a family of pairs of disjoint subsets
    (L_k, R_k) such that every distinct pair of vertices {u, v} is covered by exactly one bipartite graph. -/
def IsCompleteBipartitePartition (n m : ℕ) (L R : Fin m → Finset (Fin n)) : Prop :=
  (∀ k, Disjoint (L k) (R k)) ∧
  (∀ u v : Fin n, u ≠ v →
    ∃! k : Fin m, (u ∈ L k ∧ v ∈ R k) ∨ (u ∈ R k ∧ v ∈ L k))

/-- The left vertex of the k-th star in the canonical star decomposition of $. -/
def starPartition_L (n : ℕ) (k : Fin (n - 1)) : Finset (Fin n) :=
  {⟨k.val, by have := k.isLt; omega⟩}

/-- The right vertices of the k-th star in the canonical star decomposition of $. -/
def starPartition_R (n : ℕ) (k : Fin (n - 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => k.val < j.val)

/-- **The Graham–Pollak Theorem (1971)**:
Every partition of the edge set of the complete graph $ into $ complete bipartite
subgraphs requires at least  - 1$ bipartite graphs ( \ge n - 1$). -/
theorem graham_pollak (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) :
    n - 1 ≤ m := sorry

/-- **Tightness of the Graham–Pollak Theorem**:
$ can be partitioned into  - 1$ complete bipartite graphs (specifically, stars). -/
theorem graham_pollak_tight (n : ℕ) :
    IsCompleteBipartitePartition n (n - 1) (starPartition_L n) (starPartition_R n) := sorry