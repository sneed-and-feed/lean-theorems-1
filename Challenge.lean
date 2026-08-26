import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Data.Fintype.Basic

open SimpleGraph
open Classical

namespace TutteOneFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A 1-factor of a simple graph `G` is a 1-regular spanning subgraph, i.e., a perfect matching. -/
def IsOneFactor {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  M.IsPerfectMatching

/-- A graph `G` has a 1-factor if there exists a spanning perfect matching. -/
def HasOneFactor (G : SimpleGraph V) : Prop :=
  ∃ M : G.Subgraph, M.IsPerfectMatching

/-- The number of odd connected components of `G \ U`. -/
noncomputable def q (G : SimpleGraph V) (U : Set V) : ℕ :=
  (((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents).ncard

/-- **Tutte's 1-Factor Theorem (Necessity Direction):**
If `G` has a 1-factor, then for every subset `U ⊆ V`, the number of odd components `q(G \ U) ≤ |U|`. -/
theorem tutte_necessity (G : SimpleGraph V) (hM : HasOneFactor G) (U : Set V) :
    q G U ≤ U.ncard := sorry

/-- **Tutte's 1-Factor Theorem (Equivalence):**
A graph `G` has a 1-factor if and only if for all subsets `U ⊆ V`, `q(G \ U) ≤ |U|`. -/
theorem tutte_1factor_theorem (G : SimpleGraph V) :
    HasOneFactor G ↔ ∀ U : Set V, q G U ≤ U.ncard := sorry

end TutteOneFactor
