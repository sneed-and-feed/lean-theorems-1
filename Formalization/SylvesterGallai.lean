import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Sylvester–Gallai Theorem (Freek Wiedijk #98)

This module provides the formalization of the **Sylvester–Gallai Theorem**
(J. J. Sylvester 1893, T. Gallai 1944, L. M. Kelly 1948).

## Mathematical Statement
Let `S` be a finite set of points in the Euclidean plane $\mathbb{R}^2$.
If not all points in `S` lie on a single straight line (i.e. `S` is non-collinear),
then there exists an **ordinary line**—a line passing through *exactly two* points of `S`.

## References
* J. J. Sylvester (1893), *Mathematical Question 11851*, Educational Times, 59:98.
* T. Gallai (1944), *Solution to Problem 4065*, American Mathematical Monthly, 51:169–171.
* L. M. Kelly (1948), *A simple proof of the Sylvester-Gallai theorem*, in Coxeter's *Projective Geometry*.
* F. Wiedijk (2008), *Formalizing 100 Theorems*, #98.
-/

noncomputable section

open scoped Classical

namespace SylvesterGallai

/-- A point in the 2D real affine plane. -/
abbrev Point := ℝ × ℝ

/-- 2D cross product (determinant) of two vectors. -/
def cross (u v : Point) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/-- 2D dot product of two vectors. -/
def dot (u v : Point) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- Squared Euclidean norm of a 2D vector. -/
def sqNorm (u : Point) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- Signed area of triangle formed by three points p, q, r. -/
def signedArea (p q r : Point) : ℝ :=
  cross (q.1 - p.1, q.2 - p.2) (r.1 - p.1, r.2 - p.2)

/-- Three points in the plane are collinear if the triangle they form has zero signed area. -/
def Collinear (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) = 0

/-- A finite set of points `S` is collinear if all triples in `S` are collinear. -/
def SetCollinear (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, Collinear p q r

/-- A line determined by two distinct points `p ≠ q`. -/
def lineThrough (p q : Point) : Set Point :=
  { r | Collinear p q r }

/-- An ordinary line with respect to a finite point set `S` is a line passing through
exactly two points of `S`. -/
def IsOrdinaryLine (S : Finset Point) (p q : Point) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ (∀ r ∈ S, Collinear p q r → r = p ∨ r = q)

lemma collinear_iff_signedArea (p q r : Point) :
    Collinear p q r ↔ signedArea p q r = 0 :=
  Iff.rfl

lemma signedArea_perm (p q r : Point) : signedArea p r q = - signedArea p q r := by
  dsimp [signedArea, cross]
  ring

lemma signedArea_cyclic (p q r : Point) : signedArea q r p = signedArea p q r := by
  dsimp [signedArea, cross]
  ring

lemma collinear_perm (p q r : Point) : Collinear p r q ↔ Collinear p q r := by
  rw [collinear_iff_signedArea, collinear_iff_signedArea, signedArea_perm, neg_eq_zero]

lemma collinear_perm_left (p q r : Point) : Collinear q p r ↔ Collinear p q r := by
  rw [collinear_iff_signedArea, collinear_iff_signedArea]
  have : signedArea q p r = - signedArea p q r := by
    dsimp [signedArea, cross]
    ring
  rw [this, neg_eq_zero]

lemma collinear_cyclic (p q r : Point) : Collinear q r p ↔ Collinear p q r := by
  rw [collinear_iff_signedArea, collinear_iff_signedArea, signedArea_cyclic]

lemma signedArea_self_left (p q : Point) : signedArea p p q = 0 := by
  dsimp [signedArea, cross]
  ring

lemma signedArea_self_right (p q : Point) : signedArea p q p = 0 := by
  dsimp [signedArea, cross]
  ring

lemma collinear_self_left (p q : Point) : Collinear p p q := by
  rw [collinear_iff_signedArea]
  exact signedArea_self_left p q

lemma collinear_self_right (p q : Point) : Collinear p q p := by
  rw [collinear_iff_signedArea]
  exact signedArea_self_right p q

lemma sqNorm_pos_of_ne {u : Point} (h : u ≠ (0, 0)) : 0 < sqNorm u := by
  dsimp [sqNorm]
  have h1 : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    contrapose! h
    ext
    · exact h.1
    · exact h.2
  rcases h1 with h1 | h2
  · have : 0 < u.1 ^ 2 := sq_pos_of_ne_zero h1
    have : 0 ≤ u.2 ^ 2 := sq_nonneg _
    linarith
  · have : 0 < u.2 ^ 2 := sq_pos_of_ne_zero h2
    have : 0 ≤ u.1 ^ 2 := sq_nonneg _
    linarith

lemma sqNorm_pos_of_points_ne {p q : Point} (h : p ≠ q) :
    0 < sqNorm (q.1 - p.1, q.2 - p.2) := by
  apply sqNorm_pos_of_ne
  intro h0
  apply h
  ext
  · linarith [congr_arg Prod.fst h0]
  · linarith [congr_arg Prod.snd h0]

lemma sqNorm_ne_zero_of_points_ne {p q : Point} (h : p ≠ q) :
    sqNorm (q.1 - p.1, q.2 - p.2) ≠ 0 :=
  (sqNorm_pos_of_points_ne h).ne'

/-- Squared Euclidean distance from point `p` to the line through `a` and `b`. -/
def distSq (p a b : Point) : ℝ :=
  (signedArea a b p) ^ 2 / sqNorm (b.1 - a.1, b.2 - a.2)

lemma distSq_pos {p a b : Point} (hab : a ≠ b) (hp : ¬ Collinear a b p) :
    0 < distSq p a b := by
  dsimp [distSq]
  have h_area_ne : signedArea a b p ≠ 0 := by
    intro h0
    apply hp
    rw [collinear_iff_signedArea]
    exact h0
  have h_num_pos : 0 < (signedArea a b p) ^ 2 := sq_pos_of_ne_zero h_area_ne
  have h_den_pos : 0 < sqNorm (b.1 - a.1, b.2 - a.2) := sqNorm_pos_of_points_ne hab
  exact div_pos h_num_pos h_den_pos

/-- Candidate triples `(p, a, b)` with `p, a, b ∈ S`, `a ≠ b`, and `p` not on line `(a, b)`. -/
def candidateTriples (S : Finset Point) : Finset (Point × (Point × Point)) :=
  (S ×ˢ (S ×ˢ S)).filter (fun ⟨p, a, b⟩ => a ≠ b ∧ ¬ Collinear a b p)

lemma candidateTriples_nonempty {S : Finset Point} (h_non_collinear : ¬ SetCollinear S) :
    (candidateTriples S).Nonempty := by
  dsimp [SetCollinear] at h_non_collinear
  have : ∃ a ∈ S, ∃ b ∈ S, ∃ p ∈ S, ¬ Collinear a b p := by
    by_contra hc
    apply h_non_collinear
    intro a ha b hb p hp
    by_contra hnp
    exact hc ⟨a, ha, b, hb, p, hp, hnp⟩
  rcases this with ⟨a, ha, b, hb, p, hp, hnp⟩
  have hab : a ≠ b := by
    rintro rfl
    exact hnp (collinear_self_left a p)
  refine ⟨⟨p, a, b⟩, ?_⟩
  rw [candidateTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
  refine ⟨⟨hp, ha, hb⟩, hab, hnp⟩

lemma collinear_param_of_collinear (a0 b0 r : Point) (hne : a0 ≠ b0) (hcol : Collinear a0 b0 r) :
    let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
    let t := dot (r.1 - a0.1, r.2 - a0.2) v / sqNorm v
    r = (a0.1 + t * v.1, a0.2 + t * v.2) := by
  intro v t
  have hv_ne : sqNorm v ≠ 0 := sqNorm_ne_zero_of_points_ne hne
  dsimp [Collinear, signedArea, cross] at hcol
  ext
  · dsimp [t, dot, sqNorm, v]
    have hv_ne' : (b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2 ≠ 0 := hv_ne
    have hX : ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
        ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) =
        (r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2) :=
      div_mul_cancel₀ _ hv_ne'
    have : (r.1 - a0.1) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) =
        (((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
        ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * (b0.1 - a0.1)) *
        ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) := by
      calc
        (r.1 - a0.1) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2)
        _ = ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) * (b0.1 - a0.1) -
            (b0.2 - a0.2) * ((b0.1 - a0.1) * (r.2 - a0.2) - (b0.2 - a0.2) * (r.1 - a0.1)) := by ring
        _ = ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) * (b0.1 - a0.1) -
            (b0.2 - a0.2) * 0 := by rw [hcol]
        _ = ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) * (b0.1 - a0.1) := by ring
        _ = (((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
            ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2)) *
            (b0.1 - a0.1) := by rw [hX]
        _ = (((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
            ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * (b0.1 - a0.1)) *
            ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) := by ring
    have h_eq := mul_right_cancel₀ hv_ne' this
    linarith
  · dsimp [t, dot, sqNorm, v]
    have hv_ne' : (b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2 ≠ 0 := hv_ne
    have hX : ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
        ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) =
        (r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2) :=
      div_mul_cancel₀ _ hv_ne'
    have : (r.2 - a0.2) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) =
        (((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
        ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * (b0.2 - a0.2)) *
        ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) := by
      calc
        (r.2 - a0.2) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2)
        _ = ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) * (b0.2 - a0.2) +
            (b0.1 - a0.1) * ((b0.1 - a0.1) * (r.2 - a0.2) - (b0.2 - a0.2) * (r.1 - a0.1)) := by ring
        _ = ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) * (b0.2 - a0.2) +
            (b0.1 - a0.1) * 0 := by rw [hcol]
        _ = ((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) * (b0.2 - a0.2) := by ring
        _ = (((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
            ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2)) *
            (b0.2 - a0.2) := by rw [hX]
        _ = (((r.1 - a0.1) * (b0.1 - a0.1) + (r.2 - a0.2) * (b0.2 - a0.2)) /
            ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) * (b0.2 - a0.2)) *
            ((b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2) := by ring
    have h_eq := mul_right_cancel₀ hv_ne' this
    linarith

lemma collinear_of_param (a0 b0 : Point) (t : ℝ) :
    let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
    Collinear a0 b0 (a0.1 + t * v.1, a0.2 + t * v.2) := by
  intro v
  rw [collinear_iff_signedArea]
  dsimp [signedArea, cross, v]
  ring

lemma collinear_iff_param (a0 b0 r : Point) (hne : a0 ≠ b0) :
    let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
    Collinear a0 b0 r ↔ ∃ t : ℝ, r = (a0.1 + t * v.1, a0.2 + t * v.2) := by
  intro v
  constructor
  · intro hcol
    refine ⟨dot (r.1 - a0.1, r.2 - a0.2) v / sqNorm v, ?_⟩
    exact collinear_param_of_collinear a0 b0 r hne hcol
  · rintro ⟨t, rfl⟩
    exact collinear_of_param a0 b0 t

lemma param_inj (a0 b0 : Point) (hne : a0 ≠ b0) (t1 t2 : ℝ) :
    let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
    (a0.1 + t1 * v.1, a0.2 + t1 * v.2) = (a0.1 + t2 * v.1, a0.2 + t2 * v.2) → t1 = t2 := by
  intro v heq
  have hv_ne : sqNorm v ≠ 0 := sqNorm_ne_zero_of_points_ne hne
  have h1 : (t1 - t2) * v.1 = 0 := by
    have hfst := congr_arg Prod.fst heq
    dsimp at hfst
    linarith
  have h2 : (t1 - t2) * v.2 = 0 := by
    have hsnd := congr_arg Prod.snd heq
    dsimp at hsnd
    linarith
  have : (t1 - t2) ^ 2 * sqNorm v = 0 := by
    dsimp [sqNorm]
    calc
      (t1 - t2) ^ 2 * (v.1 ^ 2 + v.2 ^ 2)
      _ = ((t1 - t2) * v.1) ^ 2 + ((t1 - t2) * v.2) ^ 2 := by ring
      _ = 0 ^ 2 + 0 ^ 2 := by rw [h1, h2]
      _ = 0 := by ring
  cases mul_eq_zero.mp this with
  | inl h =>
    have : t1 - t2 = 0 := sq_eq_zero_iff.mp h
    linarith
  | inr h =>
    exact False.elim (hv_ne h)

lemma signedArea_param (a0 b0 p : Point) (t1 t2 : ℝ) :
    let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
    let a : Point := (a0.1 + t1 * v.1, a0.2 + t1 * v.2)
    let b : Point := (a0.1 + t2 * v.1, a0.2 + t2 * v.2)
    signedArea p a b = (t2 - t1) * signedArea a0 b0 p := by
  intro v a b
  dsimp [signedArea, cross, a, b, v]
  ring

lemma pythagorean_decomp (a0 b0 p : Point) (hne : a0 ≠ b0) (t : ℝ) :
    let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
    let t_q := dot (p.1 - a0.1, p.2 - a0.2) v / sqNorm v
    let a : Point := (a0.1 + t * v.1, a0.2 + t * v.2)
    sqNorm (a.1 - p.1, a.2 - p.2) = (t - t_q) ^ 2 * sqNorm v + (signedArea a0 b0 p) ^ 2 / sqNorm v := by
  intro v t_q a
  have hv_ne : sqNorm v ≠ 0 := sqNorm_ne_zero_of_points_ne hne
  dsimp [sqNorm, dot, t_q, a, v, signedArea, cross]
  have hv_ne' : (b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2 ≠ 0 := hv_ne
  field_simp
  ring

lemma sq_le_sq_of_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith

lemma exists_closer_pair_sorted (t1 t2 t3 tq : ℝ) (h12 : t1 < t2) (h23 : t2 < t3) :
    ∃ (ti tj : ℝ), (ti = t1 ∨ ti = t2 ∨ ti = t3) ∧
                   (tj = t1 ∨ tj = t2 ∨ tj = t3) ∧
                   ti ≠ tj ∧
                   (tj - ti) ^ 2 ≤ (ti - tq) ^ 2 := by
  by_cases hq : tq ≤ t2
  · refine ⟨t3, t2, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), h23.ne', ?_⟩
    have h_diff_pos : 0 ≤ t3 - t2 := by linarith
    have h_le : t3 - t2 ≤ t3 - tq := by linarith
    have h_sq : (t3 - t2) ^ 2 ≤ (t3 - tq) ^ 2 := sq_le_sq_of_le_of_nonneg h_diff_pos h_le
    have : (t2 - t3) ^ 2 = (t3 - t2) ^ 2 := by ring
    linarith
  · have hq_lt : t2 < tq := not_le.mp hq
    refine ⟨t1, t2, Or.inl rfl, Or.inr (Or.inl rfl), h12.ne, ?_⟩
    have h_diff_pos : 0 ≤ t2 - t1 := by linarith
    have h_le : t2 - t1 ≤ tq - t1 := by linarith
    have h_sq : (t2 - t1) ^ 2 ≤ (tq - t1) ^ 2 := sq_le_sq_of_le_of_nonneg h_diff_pos h_le
    have : (t1 - tq) ^ 2 = (tq - t1) ^ 2 := by ring
    linarith

lemma exists_closer_pair_1d (t1 t2 t3 tq : ℝ) (h12 : t1 ≠ t2) (h13 : t1 ≠ t3) (h23 : t2 ≠ t3) :
    ∃ (ti tj : ℝ), (ti = t1 ∨ ti = t2 ∨ ti = t3) ∧
                   (tj = t1 ∨ tj = t2 ∨ tj = t3) ∧
                   ti ≠ tj ∧
                   (tj - ti) ^ 2 ≤ (ti - tq) ^ 2 := by
  rcases lt_or_gt_of_ne h12 with h12_lt | h12_gt
  · rcases lt_or_gt_of_ne h23 with h23_lt | h23_gt
    · exact exists_closer_pair_sorted t1 t2 t3 tq h12_lt h23_lt
    · rcases lt_or_gt_of_ne h13 with h13_lt | h13_gt
      · rcases exists_closer_pair_sorted t1 t3 t2 tq h13_lt h23_gt with ⟨ti, tj, hti, htj, hne, hle⟩
        refine ⟨ti, tj, ?_, ?_, hne, hle⟩
        · rcases hti with rfl | rfl | rfl <;> simp
        · rcases htj with rfl | rfl | rfl <;> simp
      · rcases exists_closer_pair_sorted t3 t1 t2 tq h13_gt h12_lt with ⟨ti, tj, hti, htj, hne, hle⟩
        refine ⟨ti, tj, ?_, ?_, hne, hle⟩
        · rcases hti with rfl | rfl | rfl <;> simp
        · rcases htj with rfl | rfl | rfl <;> simp
  · rcases lt_or_gt_of_ne h13 with h13_lt | h13_gt
    · rcases exists_closer_pair_sorted t2 t1 t3 tq h12_gt h13_lt with ⟨ti, tj, hti, htj, hne, hle⟩
      refine ⟨ti, tj, ?_, ?_, hne, hle⟩
      · rcases hti with rfl | rfl | rfl <;> simp
      · rcases htj with rfl | rfl | rfl <;> simp
    · rcases lt_or_gt_of_ne h23 with h23_lt | h23_gt
      · rcases exists_closer_pair_sorted t2 t3 t1 tq h23_lt h13_gt with ⟨ti, tj, hti, htj, hne, hle⟩
        refine ⟨ti, tj, ?_, ?_, hne, hle⟩
        · rcases hti with rfl | rfl | rfl <;> simp
        · rcases htj with rfl | rfl | rfl <;> simp
      · rcases exists_closer_pair_sorted t3 t2 t1 tq h23_gt h12_gt with ⟨ti, tj, hti, htj, hne, hle⟩
        refine ⟨ti, tj, ?_, ?_, hne, hle⟩
        · rcases hti with rfl | rfl | rfl <;> simp
        · rcases htj with rfl | rfl | rfl <;> simp

/-- **The Sylvester–Gallai Theorem (Freek Wiedijk #98):**
Every finite, non-collinear set of points in the real Euclidean plane contains an ordinary line. -/
theorem sylvester_gallai (S : Finset Point) (_h_card : 3 ≤ S.card) (h_non_collinear : ¬ SetCollinear S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ IsOrdinaryLine S p q := by
  have h_ne : (candidateTriples S).Nonempty := candidateTriples_nonempty h_non_collinear
  rcases Finset.exists_min_image (candidateTriples S) (fun ⟨p, a, b⟩ => distSq p a b) h_ne with
    ⟨⟨p0, a0, b0⟩, h_mem_min, h_le_min⟩
  rw [candidateTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at h_mem_min
  rcases h_mem_min with ⟨⟨hp0, ha0, hb0⟩, ha0b0_ne, h_p0_not_collinear⟩
  refine ⟨a0, ha0, b0, hb0, ha0b0_ne, ?_⟩
  refine ⟨ha0, hb0, ha0b0_ne, ?_⟩
  intro c hc h_collinear_c
  by_contra hc_not_a0b0
  have hc_ne_a0 : c ≠ a0 := by
    intro hc_a0
    apply hc_not_a0b0
    exact Or.inl hc_a0
  have hc_ne_b0 : c ≠ b0 := by
    intro hc_b0
    apply hc_not_a0b0
    exact Or.inr hc_b0
  let v : Point := (b0.1 - a0.1, b0.2 - a0.2)
  have hv_ne : sqNorm v ≠ 0 := sqNorm_ne_zero_of_points_ne ha0b0_ne
  let t_c := dot (c.1 - a0.1, c.2 - a0.2) v / sqNorm v
  have hc_param : c = (a0.1 + t_c * v.1, a0.2 + t_c * v.2) :=
    collinear_param_of_collinear a0 b0 c ha0b0_ne h_collinear_c
  have ha0_param : a0 = (a0.1 + 0 * v.1, a0.2 + 0 * v.2) := by
    dsimp [v]; ext <;> ring
  have hb0_param : b0 = (a0.1 + 1 * v.1, a0.2 + 1 * v.2) := by
    dsimp [v]; ext <;> ring
  have ht_0_1 : (0 : ℝ) ≠ 1 := by norm_num
  have ht_0_c : (0 : ℝ) ≠ t_c := by
    intro h_eq
    apply hc_ne_a0
    rw [hc_param, ← h_eq, ← ha0_param]
  have ht_1_c : (1 : ℝ) ≠ t_c := by
    intro h_eq
    apply hc_ne_b0
    rw [hc_param, ← h_eq, ← hb0_param]
  let t_q := dot (p0.1 - a0.1, p0.2 - a0.2) v / sqNorm v
  rcases exists_closer_pair_1d 0 1 t_c t_q ht_0_1 ht_0_c ht_1_c with ⟨ti, tj, hti, htj, hti_tj_ne, h_sq_le⟩
  let a : Point := (a0.1 + ti * v.1, a0.2 + ti * v.2)
  let b : Point := (a0.1 + tj * v.1, a0.2 + tj * v.2)
  have ha_mem_S : a ∈ S := by
    dsimp [a]
    rcases hti with rfl | rfl | rfl
    · rw [← ha0_param]; exact ha0
    · rw [← hb0_param]; exact hb0
    · rw [← hc_param]; exact hc
  have hb_mem_S : b ∈ S := by
    dsimp [b]
    rcases htj with rfl | rfl | rfl
    · rw [← ha0_param]; exact ha0
    · rw [← hb0_param]; exact hb0
    · rw [← hc_param]; exact hc
  have hab_ne : a ≠ b := by
    intro h_ab_eq
    have : ti = tj := param_inj a0 b0 ha0b0_ne ti tj h_ab_eq
    exact hti_tj_ne this
  have hp0_a_ne : p0 ≠ a := by
    rintro rfl
    apply h_p0_not_collinear
    dsimp [a]
    rcases hti with rfl | rfl | rfl
    · have : (a0.1 + 0 * v.1, a0.2 + 0 * v.2) = a0 := ha0_param.symm
      rw [this]
      exact collinear_self_right a0 b0
    · have : (a0.1 + 1 * v.1, a0.2 + 1 * v.2) = b0 := hb0_param.symm
      rw [this]
      rw [collinear_iff_signedArea]
      dsimp [signedArea, cross]
      ring
    · have : (a0.1 + t_c * v.1, a0.2 + t_c * v.2) = c := hc_param.symm
      rw [this]
      exact h_collinear_c
  have h_not_collinear_p0_a_b : ¬ Collinear p0 a b := by
    intro h_col
    have h_area : signedArea p0 a b = 0 := h_col
    have h_param_area : signedArea p0 a b = (tj - ti) * signedArea a0 b0 p0 := by
      dsimp [signedArea, cross, a, b, v]
      ring
    rw [h_param_area] at h_area
    cases mul_eq_zero.mp h_area with
    | inl h_t =>
      have : ti = tj := by linarith
      exact hti_tj_ne this
    | inr h_p0 =>
      apply h_p0_not_collinear
      rw [collinear_iff_signedArea]
      exact h_p0
  have h_pair_mem : (⟨b, p0, a⟩ : Point × (Point × Point)) ∈ candidateTriples S := by
    rw [candidateTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_product]
    refine ⟨⟨hb_mem_S, hp0, ha_mem_S⟩, hp0_a_ne, h_not_collinear_p0_a_b⟩
  have h_min_le := h_le_min ⟨b, p0, a⟩ h_pair_mem
  have h_area_a0b0p0_ne : signedArea a0 b0 p0 ≠ 0 := by
    intro h0
    apply h_p0_not_collinear
    rw [collinear_iff_signedArea]
    exact h0
  have h_sq_area_pos : 0 < (signedArea a0 b0 p0) ^ 2 := sq_pos_of_ne_zero h_area_a0b0p0_ne
  have h_sqNorm_v_pos : 0 < sqNorm v := sqNorm_pos_of_points_ne ha0b0_ne
  have h_strict_less : distSq b p0 a < distSq p0 a0 b0 := by
    dsimp [distSq]
    have h_area_b_p0_a : signedArea p0 a b = (tj - ti) * signedArea a0 b0 p0 := by
      dsimp [signedArea, cross, a, b, v]
      ring
    rw [h_area_b_p0_a]
    have h_num : ((tj - ti) * signedArea a0 b0 p0) ^ 2 = (tj - ti) ^ 2 * (signedArea a0 b0 p0) ^ 2 := by ring
    rw [h_num]
    have h_pyth : sqNorm (a.1 - p0.1, a.2 - p0.2) = (ti - t_q) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v := by
      dsimp [sqNorm, dot, t_q, a, v, signedArea, cross]
      have hv_ne' : (b0.1 - a0.1) ^ 2 + (b0.2 - a0.2) ^ 2 ≠ 0 := hv_ne
      field_simp
      ring
    rw [h_pyth]
    have h_sq_diff_pos : 0 < (tj - ti) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hti_tj_ne))
    have h_den_left : (tj - ti) ^ 2 * sqNorm v ≤ (ti - t_q) ^ 2 * sqNorm v := by
      nlinarith
    have h_offset_pos : 0 < (signedArea a0 b0 p0) ^ 2 / sqNorm v := div_pos h_sq_area_pos h_sqNorm_v_pos
    have h_den_pos : 0 < (ti - t_q) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v := by
      have : 0 ≤ (ti - t_q) ^ 2 * sqNorm v := by positivity
      linarith
    have h_frac_le : (tj - ti) ^ 2 * (signedArea a0 b0 p0) ^ 2 / ((ti - t_q) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v) ≤
        (tj - ti) ^ 2 * (signedArea a0 b0 p0) ^ 2 / ((tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v) := by
      apply div_le_div_of_nonneg_left (by positivity)
      · have : 0 ≤ (tj - ti) ^ 2 * sqNorm v := by positivity
        linarith
      · linarith
    have h_frac_lt : (tj - ti) ^ 2 * (signedArea a0 b0 p0) ^ 2 / ((tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v) <
        (signedArea a0 b0 p0) ^ 2 / sqNorm v := by
      have h_alg : (signedArea a0 b0 p0) ^ 2 / sqNorm v -
          (tj - ti) ^ 2 * (signedArea a0 b0 p0) ^ 2 / ((tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v) =
          ((signedArea a0 b0 p0) ^ 2 / sqNorm v) * ((signedArea a0 b0 p0) ^ 2 / sqNorm v) /
          ((tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v) := by
        have h_d1 : sqNorm v ≠ 0 := hv_ne
        have h_d2 : (tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v ≠ 0 := by
          have : 0 < (tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v := by
            have : 0 ≤ (tj - ti) ^ 2 * sqNorm v := by positivity
            linarith
          linarith
        field_simp
        ring
      have h_diff_pos : 0 < ((signedArea a0 b0 p0) ^ 2 / sqNorm v) * ((signedArea a0 b0 p0) ^ 2 / sqNorm v) /
          ((tj - ti) ^ 2 * sqNorm v + (signedArea a0 b0 p0) ^ 2 / sqNorm v) := by
        apply div_pos
        · exact mul_pos h_offset_pos h_offset_pos
        · have : 0 ≤ (tj - ti) ^ 2 * sqNorm v := by positivity
          linarith
      linarith
    exact lt_of_le_of_lt h_frac_le h_frac_lt
  linarith

#print axioms sylvester_gallai

end SylvesterGallai

