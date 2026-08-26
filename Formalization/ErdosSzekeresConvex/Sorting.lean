import Formalization.ErdosSzekeresConvex.Orientation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

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
  simp only [Finset.mem_image] at hp hq hr
  obtain ⟨p0, hp0, rfl⟩ := hp; obtain ⟨q0, hq0, rfl⟩ := hq; obtain ⟨r0, hr0, rfl⟩ := hr
  rw [orientationDet_rotate2D c s h_unit]
  exact h_gen p0 q0 r0 hp0 hq0 hr0 (hpq ∘ congrArg _) (hqr ∘ congrArg _) (hpr ∘ congrArg _)

/-- Lexicographic ordering on ℝ² by x then y, used to canonicalize point sorting. -/
def lexLE (p q : Point2D) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

noncomputable instance : DecidableRel lexLE := Classical.decRel lexLE

instance : IsTrans Point2D lexLE := ⟨by
  rintro a b c (h1|⟨h1,h2⟩) (h3|⟨h3,h4⟩) <;> unfold lexLE
  · exact Or.inl (h1.trans h3)
  · exact Or.inl (h3 ▸ h1)
  · exact Or.inl (h1 ▸ h3)
  · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩
⟩

instance : Std.Antisymm lexLE := ⟨by
  rintro a b (h1|⟨h1,h2⟩) (h3|⟨h3,h4⟩) <;> try linarith
  ext <;> linarith
⟩

instance : Std.Total lexLE := ⟨by
  intro a b
  rcases lt_trichotomy a.1 b.1 with h|h|h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.2 b.2 with h2|h2
    · exact Or.inl (Or.inr ⟨h, h2⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h2⟩)
  · exact Or.inr (Or.inl h)
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
  · ext x; simp
  · intro i hi
    have h_pair := List.pairwise_iff_get.mp (Finset.pairwise_sort S lexLE) ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp)
    have h_ne : (S.sort lexLE).get ⟨i, by omega⟩ ≠ (S.sort lexLE).get ⟨i + 1, hi⟩ := fun heq => by
      have h_inj := List.nodup_iff_injective_get.mp (Finset.sort_nodup S lexLE) heq
      have : i = i + 1 := by injection h_inj
      omega
    have hm1 : (S.sort lexLE).get ⟨i, by omega⟩ ∈ S := (Finset.mem_sort lexLE).mp (List.get_mem ..)
    have hm2 : (S.sort lexLE).get ⟨i + 1, hi⟩ ∈ S := (Finset.mem_sort lexLE).mp (List.get_mem ..)
    rcases h_pair with h_lt | ⟨h_eq, _⟩
    · exact h_lt
    · exact False.elim (hdist _ _ hm1 hm2 h_ne h_eq)
