import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Basic

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of subsets whose pairwise intersection cardinalities mod p lie in L. -/
structure ModuloPIntersectingFamily (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p)) where
  /-- The family of subsets -/
  F : Finset (Finset α)
  /-- Forbidden self-size residue: |A| mod p ∉ L -/
  h_self : ∀ A ∈ F, (A.card : ZMod p) ∉ L
  /-- Allowed pairwise intersection residues: |A ∩ B| mod p ∈ L for A ≠ B -/
  h_inter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ZMod p) ∈ L

/-- General Frankl–Wilson Theorem (1981):
    |F| ≤ ∑_{i=0}^s Nat.choose n i where s = |L|. -/
theorem frankl_wilson_general (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L) :
    fam.F.card ≤ ∑ i ∈ Finset.range (L.card + 1), Nat.choose (Fintype.card α) i := sorry

/-- Uniform Cardinality Frankl–Wilson Theorem (1981):
    If all subsets in F have equal size k with (k : ZMod p) ∉ L, and k mod p ≠ j mod p for all j < |L|,
    then |F| ≤ Nat.choose n s. -/
theorem frankl_wilson_uniform (p : ℕ) [Fact (Nat.Prime p)] (L : Finset (ZMod p))
    (fam : ModuloPIntersectingFamily (α := α) p L)
    (k : ℕ) (h_uniform : ∀ A ∈ fam.F, A.card = k)
    (hk_diff : ∀ j < L.card, (k : ZMod p) ≠ (j : ZMod p)) :
    fam.F.card ≤ Nat.choose (Fintype.card α) L.card := sorry
