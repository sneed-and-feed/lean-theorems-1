import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Frankl–Wilson Theorem on Modulo-p Intersecting Families (1981)

**The Frankl–Wilson Theorem (Péter Frankl & Richard M. Wilson, 1981)** is a landmark triumph
of the linear algebra method in extremal combinatorics.

## Mathematical Statement
Let $p$ be a prime, and let $L \subset \{0, 1, \dots, p-1\}$ be a set of $s = |L|$ residues modulo $p$.
Let $\mathcal{F}$ be a family of subsets of an $n$-element universe such that:
1. $|A| \pmod p \notin L$ for all $A \in \mathcal{F}$
2. $|A \cap B| \pmod p \in L$ for all distinct $A \ne B \in \mathcal{F}$.

Then the family size satisfies the polynomial dimension bound:
$$|\mathcal{F}| \le \sum_{i=0}^s \binom{n}{i}$$

When all subsets in $\mathcal{F}$ have the same uniform cardinality $k$, the bound sharpens to:
$$|\mathcal{F}| \le \binom{n}{s}$$

## Applications & Borsuk's Conjecture
In 1993, Jeff Kahn and Gil Kalai utilized the Frankl–Wilson theorem to construct high-dimensional
point sets in $\mathbb{R}^d$ that require exponentially many pieces to partition into sets of
smaller diameter, famously **disproving Borsuk's Conjecture (1933)**.
-/

-- ============================================================================
-- Section 1: Modulo-p Intersection Families
-- ============================================================================

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of subsets whose pairwise intersection cardinalities mod p lie in L. -/
structure ModuloPIntersectingFamily (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p)) where
  /-- The family of subsets -/
  F : Finset (Finset α)
  /-- Forbidden self-size residue: |A| mod p ∉ L -/
  h_self : ∀ A ∈ F, (A.card : ZMod p) ∉ L
  /-- Allowed pairwise intersection residues: |A ∩ B| mod p ∈ L for A ≠ B -/
  h_inter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L

-- ============================================================================
-- Section 2: Frankl–Wilson Dimension Bound
-- ============================================================================

/-- General Frankl–Wilson Theorem (1981):
    |F| ≤ ∑_{i=0}^s Nat.choose n i where s = |L|. -/
theorem frankl_wilson_general (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L) :
    fam.F.card ≤ ∑ i ∈ Finset.range (L.card + 1), Nat.choose (Fintype.card α) i := by
  sorry

/-- Uniform Cardinality Frankl–Wilson Theorem:
    If all subsets in F have equal size k with (k : ZMod p) ∉ L, then |F| ≤ Nat.choose n s. -/
theorem frankl_wilson_uniform (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L)
    (k : ℕ) (h_uniform : ∀ A ∈ fam.F, A.card = k) :
    fam.F.card ≤ Nat.choose (Fintype.card α) L.card := by
  sorry