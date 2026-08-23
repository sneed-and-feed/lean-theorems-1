import Formalization.ErdosSzekeresConvex.Orientation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# 2D Plane Rotation, Lexicographical Sorting, and Distinct X Coordinates

This module formalizes:
1. **Plane Rotations:** `rotate2D`, invariance of orientation determinants `orientationDet_rotate2D`,
   injectivity `rotate2D_injective`, and preservation of general position `inGeneralPosition_rotate2D`.
2. **Lexicographical Ordering:** `lexLE` on $\mathbb{R}^2$ (with `IsTrans`, `Std.Antisymm`, `Std.Total` instances).
3. **Distinct X Coordinates & Sorting:** `HasDistinctX`, `HasDistinctX.subset`, and the key sorting lemma
   `exists_x_sorted` which transforms any finite point set with distinct $x$-coordinates into a strictly
   $x$-monotone list without duplicates.
-/

/-- 2D rotation of a point parameterized by direction vector `(c, s)` on the unit circle `c^2 + s^2 = 1`. -/
def rotate2D (c s : ℝ) (p : Point2D) : Point2D :=
  (p.1 * c - p.2 * s, p.1 * s + p.2 * c)

/-- 2D plane rotations preserve orientation determinants algebraically. -/
lemma orientationDet_rotate2D (c s : ℝ) (h_unit : c^2 + s^2 = 1) (p q r : Point2D) :
    orientationDet (rotate2D c s p) (rotate2D c s q) (rotate2D c s r) = orientationDet p q r := by
  dsimp [orientationDet, rotate2D]
  linear_combination
    (p.1 * q.2 - p.1 * r.2 - p.2 * q.1 + p.2 * r.1 + q.1 * r.2 - q.2 * r.1) * h_unit

/-- 2D plane rotations are injective. -/
lemma rotate2D_injective (c s : ℝ) (h_unit : c^2 + s^2 = 1) :
    Function.Injective (rotate2D c s) := by
  intro p q heq
  dsimp [rotate2D] at heq
  obtain ⟨hx, hy⟩ := Prod.ext_iff.mp heq
  ext
  · linear_combination c * hx + s * hy - (p.1 - q.1) * h_unit
  · linear_combination (-s) * hx + c * hy - (p.2 - q.2) * h_unit

/-- 2D plane rotations preserve the general position property of point sets. -/
lemma inGeneralPosition_rotate2D (S : Finset Point2D) (c s : ℝ) (h_unit : c^2 + s^2 = 1)
    (h_gen : InGeneralPosition S) :
    InGeneralPosition (S.image (rotate2D c s)) := by
  intro p q r hp hq hr hpq hqr hpr
  obtain ⟨p0, hp0_in, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q0, hq0_in, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨r0, hr0_in, rfl⟩ := Finset.mem_image.mp hr
  have hpq0 : p0 ≠ q0 := fun heq => hpq (congrArg (rotate2D c s) heq)
  have hqr0 : q0 ≠ r0 := fun heq => hqr (congrArg (rotate2D c s) heq)
  have hpr0 : p0 ≠ r0 := fun heq => hpr (congrArg (rotate2D c s) heq)
  rw [orientationDet_rotate2D c s h_unit]
  exact h_gen p0 q0 r0 hp0_in hq0_in hr0_in hpq0 hqr0 hpr0

/-- Lexicographic ordering on ℝ² by x then y, used to canonicalize point sorting. -/
def lexLE (p q : Point2D) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

noncomputable instance : DecidableRel lexLE := Classical.decRel lexLE

instance : IsTrans Point2D lexLE := ⟨by
  intro a b c hab hbc
  dsimp [lexLE] at *
  rcases hab with ha1 | ⟨ha1, ha2⟩
  · rcases hbc with hb1 | ⟨hb1, hb2⟩
    · exact Or.inl (lt_trans ha1 hb1)
    · exact Or.inl (by linarith)
  · rcases hbc with hb1 | ⟨hb1, hb2⟩
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith⟩
⟩

instance : Std.Antisymm lexLE := ⟨by
  intro a b hab hba
  dsimp [lexLE] at *
  rcases hab with ha1 | ⟨ha1, ha2⟩
  · rcases hba with hb1 | ⟨hb1, hb2⟩
    · linarith
    · linarith
  · rcases hba with hb1 | ⟨hb1, hb2⟩
    · linarith
    · ext
      · exact ha1
      · linarith
⟩

instance : Std.Total lexLE := ⟨by
  intro a b
  dsimp [lexLE]
  rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
  · exact Or.inl (Or.inl hlt)
  · rcases le_total a.2 b.2 with hle | hge
    · exact Or.inl (Or.inr ⟨heq, hle⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, hge⟩)
  · exact Or.inr (Or.inl hgt)
⟩

/-- Predicate asserting that a set of points has mutually distinct x-coordinates. -/
def HasDistinctX (S : Finset Point2D) : Prop :=
  ∀ p q, p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1

lemma HasDistinctX.subset {S T : Finset Point2D} (h : HasDistinctX S) (hsub : T ⊆ S) :
    HasDistinctX T :=
  fun p q hp hq => h p q (hsub hp) (hsub hq)

/-- Any finite set of points with distinct x-coordinates can be sorted into a strictly x-monotone list. -/
lemma exists_x_sorted (S : Finset Point2D) (hdist : HasDistinctX S) :
    ∃ L : List Point2D, L.Nodup ∧ L.toFinset = S ∧ L.length = S.card ∧
      ∀ i (hi : i + 1 < L.length), (L.get ⟨i, by omega⟩).1 < (L.get ⟨i + 1, by omega⟩).1 := by
  refine ⟨S.sort lexLE, Finset.sort_nodup S lexLE, ?_, Finset.length_sort lexLE, ?_⟩
  · ext x
    rw [List.mem_toFinset, Finset.mem_sort lexLE]
  · intro i hi
    have h_sorted := Finset.pairwise_sort S lexLE
    have hi_len : i + 1 < (S.sort lexLE).length := hi
    have h_pair := List.pairwise_iff_get.mp h_sorted ⟨i, by omega⟩ ⟨i + 1, hi_len⟩ (by simp)
    dsimp at h_pair
    have h_ne : (S.sort lexLE).get ⟨i, by omega⟩ ≠ (S.sort lexLE).get ⟨i + 1, by omega⟩ := by
      intro heq
      have h_inj := List.nodup_iff_injective_get.mp (Finset.sort_nodup S lexLE) heq
      have : i = i + 1 := by injection h_inj
      omega
    have h_mem1 : (S.sort lexLE).get ⟨i, by omega⟩ ∈ S := by
      rw [← Finset.mem_sort lexLE]
      exact List.get_mem ..
    have h_mem2 : (S.sort lexLE).get ⟨i + 1, by omega⟩ ∈ S := by
      rw [← Finset.mem_sort lexLE]
      exact List.get_mem ..
    have h_x_ne := hdist _ _ h_mem1 h_mem2 h_ne
    rcases h_pair with h_lt | ⟨h_eq, h_y⟩
    · exact h_lt
    · exact False.elim (h_x_ne h_eq)
