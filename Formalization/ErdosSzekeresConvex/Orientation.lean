import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# Planar Orientations, General Position, and Halfspace Separation

This module establishes the foundational geometric primitives for the
Erdős–Szekeres theorem in $\mathbb{R}^2$:
- `Point2D`: 2D Euclidean plane points $(\mathbb{R} \times \mathbb{R})$.
- `orientationDet`: signed area / orientation determinant of 3 points.
- `InGeneralPosition`: predicate asserting no three points are collinear.
- Determinant symmetries (`orientationDet_perm`, `orientationDet_cyclic`, `orientationDet_sum_triangle`, `orientationDet_self_left/right/mid`).
- Affine combination formula (`orientationDet_smul_add_smul`).
- Convexity of halfspaces (`convex_halfspace_gt/lt/ge/le/x_gt/x_lt`).
- Strict separation lemmas for convex hulls (`not_mem_convexHull_of_separated_pos/neg/x_min/x_max`).
- `FormsConvexPolygon`: vertex definition of strictly convex $k$-gons.
-/

/-- A point in the 2D Euclidean plane. -/
abbrev Point2D := ℝ × ℝ

/-- Signed area / orientation determinant of three points `p, q, r`. -/
def orientationDet (p q r : Point2D) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- Predicate asserting that a set of points is in general position (no three points collinear). -/
def InGeneralPosition (S : Finset Point2D) : Prop :=
  ∀ p q r, p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → p ≠ r →
    orientationDet p q r ≠ 0

lemma orientationDet_perm (p q r : Point2D) :
    orientationDet p r q = - orientationDet p q r := by
  dsimp [orientationDet]; ring

lemma orientationDet_cyclic (p q r : Point2D) :
    orientationDet q r p = orientationDet p q r := by
  dsimp [orientationDet]; ring

lemma orientationDet_sum_triangle (p q r s : Point2D) :
    orientationDet p q s + orientationDet q r s + orientationDet r p s = orientationDet p q r := by
  dsimp [orientationDet]; ring

lemma orientationDet_self_left (p q : Point2D) :
    orientationDet p p q = 0 := by
  dsimp [orientationDet]; ring

lemma orientationDet_self_right (p q : Point2D) :
    orientationDet p q p = 0 := by
  dsimp [orientationDet]; ring

lemma orientationDet_self_mid (p q : Point2D) :
    orientationDet p q q = 0 := by
  dsimp [orientationDet]; ring

lemma orientationDet_smul_add_smul (a b u v : Point2D) (w1 w2 : ℝ) (hw : w1 + w2 = 1) :
    orientationDet a b (w1 • u + w2 • v) =
      w1 * orientationDet a b u + w2 * orientationDet a b v := by
  dsimp [orientationDet]; linear_combination (b.1 * a.2 - a.1 * b.2) * hw

lemma convex_halfspace_gt (a b : Point2D) :
    Convex ℝ {p : Point2D | 0 < orientationDet a b p} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rw [orientationDet_smul_add_smul a b u v w1 w2 hw]
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · positivity

lemma convex_halfspace_lt (a b : Point2D) :
    Convex ℝ {p : Point2D | orientationDet a b p < 0} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rw [orientationDet_smul_add_smul a b u v w1 w2 hw]
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · have h1 : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
    have : w2 * orientationDet a b v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw2 (le_of_lt hv)
    have : w1 * orientationDet a b u < 0 := mul_neg_of_pos_of_neg h1 hu
    linarith

lemma not_mem_convexHull_of_separated_pos (T : Finset Point2D) (p a b : Point2D)
    (hp : orientationDet a b p ≤ 0)
    (hT : ∀ t ∈ T, 0 < orientationDet a b t) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_conv := convexHull_min (fun t ht => hT t ht) (convex_halfspace_gt a b)
  exact not_le.mpr (h_conv h_mem) hp

lemma convex_halfspace_ge (a b : Point2D) :
    Convex ℝ {p : Point2D | 0 ≤ orientationDet a b p} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rw [orientationDet_smul_add_smul a b u v w1 w2 hw]
  positivity

lemma not_mem_convexHull_of_separated_pos_ge (T : Finset Point2D) (p a b : Point2D)
    (hp : orientationDet a b p < 0)
    (hT : ∀ t ∈ T, 0 ≤ orientationDet a b t) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_conv := convexHull_min (fun t ht => hT t ht) (convex_halfspace_ge a b)
  exact not_le.mpr hp (h_conv h_mem)

lemma convex_halfspace_le (a b : Point2D) :
    Convex ℝ {p : Point2D | orientationDet a b p ≤ 0} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rw [orientationDet_smul_add_smul a b u v w1 w2 hw]
  have : w1 * orientationDet a b u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw1 hu
  have : w2 * orientationDet a b v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw2 hv
  linarith

lemma not_mem_convexHull_of_separated_neg_le (T : Finset Point2D) (p a b : Point2D)
    (hp : 0 < orientationDet a b p)
    (hT : ∀ t ∈ T, orientationDet a b t ≤ 0) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_conv := convexHull_min (fun t ht => hT t ht) (convex_halfspace_le a b)
  exact not_le.mpr hp (h_conv h_mem)

lemma convex_halfspace_x_gt (x0 : ℝ) :
    Convex ℝ {p : Point2D | x0 < p.1} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · rcases eq_or_ne w2 0 with rfl | hw2_pos
    · have hw1_eq : w1 = 1 := by linarith
      subst hw1_eq
      have : (1 : ℝ) * u.1 + 0 * v.1 = u.1 := by ring
      rw [this]
      exact hu
    · have h1 : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
      have h2 : 0 < w2 := lt_of_le_of_ne hw2 (Ne.symm hw2_pos)
      calc x0 = (w1 + w2) * x0 := by rw [hw, one_mul]
        _ = w1 * x0 + w2 * x0 := by ring
        _ < w1 * u.1 + w2 * v.1 := add_lt_add (mul_lt_mul_of_pos_left hu h1) (mul_lt_mul_of_pos_left hv h2)

lemma convex_halfspace_x_lt (x0 : ℝ) :
    Convex ℝ {p : Point2D | p.1 < x0} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · rcases eq_or_ne w2 0 with rfl | hw2_pos
    · have hw1_eq : w1 = 1 := by linarith
      subst hw1_eq
      have : (1 : ℝ) * u.1 + 0 * v.1 = u.1 := by ring
      rw [this]
      exact hu
    · have h1 : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
      have h2 : 0 < w2 := lt_of_le_of_ne hw2 (Ne.symm hw2_pos)
      calc w1 * u.1 + w2 * v.1 < w1 * x0 + w2 * x0 := add_lt_add (mul_lt_mul_of_pos_left hu h1) (mul_lt_mul_of_pos_left hv h2)
        _ = (w1 + w2) * x0 := by ring
        _ = x0 := by rw [hw, one_mul]

lemma not_mem_convexHull_of_x_min (T : Finset Point2D) (p : Point2D)
    (hT : ∀ t ∈ T, p.1 < t.1) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_conv := convexHull_min (fun t ht => hT t ht) (convex_halfspace_x_gt p.1)
  exact not_le.mpr (h_conv h_mem) (le_refl p.1)

lemma not_mem_convexHull_of_x_max (T : Finset Point2D) (p : Point2D)
    (hT : ∀ t ∈ T, t.1 < p.1) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_conv := convexHull_min (fun t ht => hT t ht) (convex_halfspace_x_lt p.1)
  exact not_le.mpr (h_conv h_mem) (le_refl p.1)

/-- Predicate asserting that a subset of k points forms the vertex set of a strictly convex k-gon. -/
def FormsConvexPolygon (S : Finset Point2D) (k : ℕ) : Prop :=
  ∃ (poly : Finset Point2D), poly ⊆ S ∧ poly.card = k ∧
    ∀ p ∈ poly, p ∉ convexHull ℝ (poly \ {p} : Set Point2D)
