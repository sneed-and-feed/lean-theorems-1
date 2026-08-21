import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Kneser's Conjecture / Lovász's Theorem (1978)

**Kneser's Conjecture (Martin Kneser, 1955)**, famously proven by **László Lovász (1978)**,
determines the chromatic number of the Kneser graph $\operatorname{KG}(n, k)$.

For integers $n \ge 2k \ge 2$, the **Kneser graph** $\operatorname{KG}(n, k)$ has:
- Vertices: all $k$-element subsets of $\{1, 2, \dots, n\}$
- Edges: pairs of disjoint $k$-subsets: $A \cap B = \emptyset$.

**Theorem (Lovász 1978):**
$$\chi(\operatorname{KG}(n, k)) = n - 2k + 2$$

## Mathematical Highlights & Proof Structure
1. **Upper Bound $\chi \le n - 2k + 2$:**
   Assign colors $1, 2, \dots, n - 2k + 1$ to sets containing at least one element $c \le n - 2k + 1$
   (via the minimum element), and color $n - 2k + 2$ to all remaining subsets.
   Any two subsets in the last color class are contained in $\{n - 2k + 2, \dots, n\}$
   (which has size $2k - 1$), so by the Pigeonhole Principle they cannot be disjoint.
2. **Lower Bound $\chi \ge n - 2k + 2$:**
   Lovász's topological proof via neighborhood complexes and Borsuk–Ulam,
   or Joshua Greene's (2002) combinatorial/Gale's lemma coloring proof.
-/

-- ============================================================================
-- Section 1: Definition of the Kneser Graph
-- ============================================================================

variable (α : Type*) [DecidableEq α] [Fintype α]

/-- The Kneser graph KG(α, k): vertices are k-element subsets of α,
    and two subsets are adjacent if and only if they are disjoint. -/
def kneserGraph (k : ℕ) (hk : 1 ≤ k) : SimpleGraph {s : Finset α // s.card = k} where
  Adj A B := Disjoint A.val B.val
  symm A B h := Disjoint.symm h
  loopless A h := by
    have heq : A.val ∩ A.val = ∅ := Finset.disjoint_self_iff_empty.mp h
    rw [Finset.inter_self] at heq
    have hcard := A.property
    rw [heq, Finset.card_empty] at hcard
    omega

-- ============================================================================
-- Section 2: Kneser Upper Bound (Combinatorial Partition)
-- ============================================================================

/-- The classical upper bound on the chromatic number of Kneser graphs:
    χ(KG(n, k)) ≤ n - 2k + 2. -/
theorem kneser_chromatic_le (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ (c : {s : Finset (Fin n) // s.card = k} → Fin (n - 2 * k + 2)),
      ∀ (A B : {s : Finset (Fin n) // s.card = k}),
        Disjoint A.val B.val → c A ≠ c B := by
  sorry

-- ============================================================================
-- Section 3: Lovász's Lower Bound & Chromatic Equality
-- ============================================================================

/-- Lovász's Lower Bound Theorem (1978):
    Every proper vertex coloring of KG(n, k) requires at least n - 2k + 2 colors. -/
theorem kneser_chromatic_ge (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (c : {s : Finset (Fin n) // s.card = k} → Fin m)
    (h_proper : ∀ (A B : {s : Finset (Fin n) // s.card = k}), Disjoint A.val B.val → c A ≠ c B) :
    n - 2 * k + 2 ≤ m := by
  sorry

/-- Main Theorem: Kneser's Conjecture / Lovász's Theorem (1978).
    For n ≥ 2k, the chromatic number of the Kneser graph is exactly n - 2k + 2. -/
theorem kneser_lovasz_theorem (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph (Fin n) k hk).chromaticNumber = n - 2 * k + 2 := by
  sorry