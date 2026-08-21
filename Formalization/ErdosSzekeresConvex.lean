import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# The Happy Ending Theorem (Erdős–Szekeres Convex Polygon Theorem, 1935)

**The Happy Ending Theorem (Paul Erdős & George Szekeres, 1935)**
is one of the founding results of modern discrete and combinatorial geometry.

## Mathematical Statement
For every integer $k \ge 3$, there exists a smallest integer $ES(k)$ such that any set
of at least $ES(k)$ points in the Euclidean plane $\mathbb{R}^2$ in **general position**
(no three points collinear) with distinct $x$-coordinates contains the vertices of a convex $k$-gon.

Erdős and Szekeres proved the exact upper bound:
$$ES(k) \le \binom{2k - 4}{k - 2} + 1$$
and conjectured the exact value is $ES(k) = 2^{k - 2} + 1$:
- $k = 4 \implies ES(4) = 5$ (Esther Klein's original problem)
- $k = 5 \implies ES(5) = 9$ (Kalbfleisch et al. 1970 / Makai)
- $k = 6 \implies ES(6) = 17$ (Szekeres & Peters 2006)
- Asymptotics: $2^{k - o(k)} \le ES(k) \le 2^{k + o(k)}$ (Holmsen 2020, Suk 2017).

## Distinct $x$-Coordinates (W.l.o.g. under Plane Rotation)
In Euclidean discrete geometry, the assumption that points in general position have distinct
$x$-coordinates is without loss of generality:
Given any finite point set $S \subset \mathbb{R}^2$ in general position, there are only finitely
many directions connecting pairs of points in $S$. An algebraic plane rotation
$(x, y) \mapsto (x c - y s, x s + y c)$ by any direction $(c, s) \in S^1$ not perpendicular
to any secant line yields an image configuration with mutually distinct $x$-coordinates while
preserving general position, orientation determinants, and convex hulls.

## Proof Technique (Cups and Caps / Ramsey Transition)
1. **$x$-Sorting & Distinct Coordinates:** A finite point set with distinct $x$-coordinates
   can be sorted into a strictly $x$-increasing chain via lexicographical ordering.
2. **Cup-Cap Lemma:** A sequence of points $(x_1, y_1), \dots, (x_m, y_m)$ sorted by $x$-coordinate
   forms an $a$-cup (convex downward) or a $b$-cap (convex upward).
   Any set of $\binom{a+b-4}{a-2} + 1$ points in general position contains an $a$-cup or a $b$-cap.
3. **Extreme Point Separation:** Every vertex of an $x$-monotone $k$-cup (or $k$-cap) for $k \ge 3$
   is strictly separated from the convex hull of the other vertices by affine lines (hyperplanes),
   proving that every $k$-cup and $k$-cap forms a strictly convex $k$-gon.
4. Setting $a = b = k$ yields a convex $k$-gon of size $\binom{2k-4}{k-2} + 1$.

## References
* Erdős, P., & Szekeres, G. (1935). *A combinatorial problem in geometry*. Compositio Mathematica, 2, 463–470.
* Klein, E. (1935). *Problem 1835*. Középiskolai Matematikai Lapok.
* Suk, A. (2017). *On the Erdős–Szekeres convex polygon problem*. Journal of the American Mathematical Society, 30(2), 347–353.
-/

-- ============================================================================
-- Section 1: General Position & Planar Convex Hulls
-- ============================================================================

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
  dsimp [orientationDet]
  ring

lemma orientationDet_cyclic (p q r : Point2D) :
    orientationDet q r p = orientationDet p q r := by
  dsimp [orientationDet]
  ring

lemma orientationDet_sum_triangle (p q r s : Point2D) :
    orientationDet p q s + orientationDet q r s + orientationDet r p s = orientationDet p q r := by
  dsimp [orientationDet]
  ring

lemma orientationDet_self_left (p q : Point2D) :
    orientationDet p p q = 0 := by
  dsimp [orientationDet]
  ring

lemma orientationDet_self_right (p q : Point2D) :
    orientationDet p q p = 0 := by
  dsimp [orientationDet]
  ring

lemma orientationDet_self_mid (p q : Point2D) :
    orientationDet p q q = 0 := by
  dsimp [orientationDet]
  ring

lemma orientationDet_smul_add_smul (a b u v : Point2D) (w1 w2 : ℝ) (hw : w1 + w2 = 1) :
    orientationDet a b (w1 • u + w2 • v) =
      w1 * orientationDet a b u + w2 * orientationDet a b v := by
  dsimp [orientationDet]
  linear_combination (b.1 * a.2 - a.1 * b.2) * hw

lemma convex_halfspace_gt (a b : Point2D) :
    Convex ℝ {p : Point2D | 0 < orientationDet a b p} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rw [orientationDet_smul_add_smul a b u v w1 w2 hw]
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · have hw1_gt : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
    have : 0 ≤ w2 * orientationDet a b v := mul_nonneg hw2 (le_of_lt hv)
    have : 0 < w1 * orientationDet a b u := mul_pos hw1_gt hu
    linarith

lemma convex_halfspace_lt (a b : Point2D) :
    Convex ℝ {p : Point2D | orientationDet a b p < 0} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rw [orientationDet_smul_add_smul a b u v w1 w2 hw]
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · have hw1_gt : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
    have : w2 * orientationDet a b v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw2 (le_of_lt hv)
    have : w1 * orientationDet a b u < 0 := mul_neg_of_pos_of_neg hw1_gt hu
    linarith

lemma not_mem_convexHull_of_separated_pos (T : Finset Point2D) (p a b : Point2D)
    (hp : orientationDet a b p ≤ 0)
    (hT : ∀ t ∈ T, 0 < orientationDet a b t) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_sub : (T : Set Point2D) ⊆ {q : Point2D | 0 < orientationDet a b q} := by
    intro t ht
    exact hT t (Finset.mem_coe.mp ht)
  have h_conv := convexHull_min h_sub (convex_halfspace_gt a b)
  have hp_in : p ∈ {q : Point2D | 0 < orientationDet a b q} := h_conv h_mem
  dsimp at hp_in
  linarith

lemma convex_halfspace_ge (a b : Point2D) :
    Convex ℝ {p : Point2D | 0 ≤ orientationDet a b p} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  have h1 : 0 ≤ w1 * orientationDet a b u := mul_nonneg hw1 hu
  have h2 : 0 ≤ w2 * orientationDet a b v := mul_nonneg hw2 hv
  have h_add := add_nonneg h1 h2
  have h_comb := orientationDet_smul_add_smul a b u v w1 w2 hw
  linarith

lemma not_mem_convexHull_of_separated_pos_ge (T : Finset Point2D) (p a b : Point2D)
    (hp : orientationDet a b p < 0)
    (hT : ∀ t ∈ T, 0 ≤ orientationDet a b t) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_sub : (T : Set Point2D) ⊆ {q : Point2D | 0 ≤ orientationDet a b q} := by
    intro t ht
    exact hT t (Finset.mem_coe.mp ht)
  have h_conv := convexHull_min h_sub (convex_halfspace_ge a b)
  have hp_in : p ∈ {q : Point2D | 0 ≤ orientationDet a b q} := h_conv h_mem
  dsimp at hp_in
  linarith

lemma convex_halfspace_le (a b : Point2D) :
    Convex ℝ {p : Point2D | orientationDet a b p ≤ 0} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  have h1 : w1 * orientationDet a b u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw1 hu
  have h2 : w2 * orientationDet a b v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw2 hv
  have h_add := add_nonpos h1 h2
  have h_comb := orientationDet_smul_add_smul a b u v w1 w2 hw
  linarith

lemma not_mem_convexHull_of_separated_neg_le (T : Finset Point2D) (p a b : Point2D)
    (hp : 0 < orientationDet a b p)
    (hT : ∀ t ∈ T, orientationDet a b t ≤ 0) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_sub : (T : Set Point2D) ⊆ {q : Point2D | orientationDet a b q ≤ 0} := by
    intro t ht
    exact hT t (Finset.mem_coe.mp ht)
  have h_conv := convexHull_min h_sub (convex_halfspace_le a b)
  have hp_in : p ∈ {q : Point2D | orientationDet a b q ≤ 0} := h_conv h_mem
  dsimp at hp_in
  linarith

lemma convex_halfspace_x_gt (x0 : ℝ) :
    Convex ℝ {p : Point2D | x0 < p.1} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · have hw1_gt : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
    rcases eq_or_ne w2 0 with rfl | hw2_pos
    · have hw1_eq : w1 = 1 := by linarith
      subst hw1_eq
      have : (1 : ℝ) * u.1 + 0 * v.1 = u.1 := by ring
      rw [this]
      exact hu
    · have hw2_gt : 0 < w2 := lt_of_le_of_ne hw2 (Ne.symm hw2_pos)
      have h1 : w1 * x0 < w1 * u.1 := mul_lt_mul_of_pos_left hu hw1_gt
      have h2 : w2 * x0 < w2 * v.1 := mul_lt_mul_of_pos_left hv hw2_gt
      calc x0 = (w1 + w2) * x0 := by rw [hw, one_mul]
        _ = w1 * x0 + w2 * x0 := by ring
        _ < w1 * u.1 + w2 * v.1 := add_lt_add h1 h2

lemma convex_halfspace_x_lt (x0 : ℝ) :
    Convex ℝ {p : Point2D | p.1 < x0} := by
  intro u hu v hv w1 w2 hw1 hw2 hw
  dsimp at hu hv ⊢
  rcases eq_or_ne w1 0 with rfl | hw1_pos
  · have hw2_eq : w2 = 1 := by linarith
    subst hw2_eq
    simp [hv]
  · have hw1_gt : 0 < w1 := lt_of_le_of_ne hw1 (Ne.symm hw1_pos)
    rcases eq_or_ne w2 0 with rfl | hw2_pos
    · have hw1_eq : w1 = 1 := by linarith
      subst hw1_eq
      have : (1 : ℝ) * u.1 + 0 * v.1 = u.1 := by ring
      rw [this]
      exact hu
    · have hw2_gt : 0 < w2 := lt_of_le_of_ne hw2 (Ne.symm hw2_pos)
      have h1 : w1 * u.1 < w1 * x0 := mul_lt_mul_of_pos_left hu hw1_gt
      have h2 : w2 * v.1 < w2 * x0 := mul_lt_mul_of_pos_left hv hw2_gt
      calc w1 * u.1 + w2 * v.1 < w1 * x0 + w2 * x0 := add_lt_add h1 h2
        _ = (w1 + w2) * x0 := by ring
        _ = x0 := by rw [hw, one_mul]

lemma not_mem_convexHull_of_x_min (T : Finset Point2D) (p : Point2D)
    (hT : ∀ t ∈ T, p.1 < t.1) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_sub : (T : Set Point2D) ⊆ {q : Point2D | p.1 < q.1} := by
    intro t ht
    exact hT t (Finset.mem_coe.mp ht)
  have h_conv := convexHull_min h_sub (convex_halfspace_x_gt p.1)
  have hp_in : p ∈ {q : Point2D | p.1 < q.1} := h_conv h_mem
  dsimp at hp_in
  linarith

lemma not_mem_convexHull_of_x_max (T : Finset Point2D) (p : Point2D)
    (hT : ∀ t ∈ T, t.1 < p.1) :
    p ∉ convexHull ℝ (T : Set Point2D) := by
  intro h_mem
  have h_sub : (T : Set Point2D) ⊆ {q : Point2D | q.1 < p.1} := by
    intro t ht
    exact hT t (Finset.mem_coe.mp ht)
  have h_conv := convexHull_min h_sub (convex_halfspace_x_lt p.1)
  have hp_in : p ∈ {q : Point2D | q.1 < p.1} := h_conv h_mem
  dsimp at hp_in
  linarith

/-- Predicate asserting that a subset of k points forms the vertex set of a strictly convex k-gon. -/
def FormsConvexPolygon (S : Finset Point2D) (k : ℕ) : Prop :=
  ∃ (poly : Finset Point2D), poly ⊆ S ∧ poly.card = k ∧
    ∀ p ∈ poly, p ∉ convexHull ℝ (poly \ {p} : Set Point2D)

-- ============================================================================
-- Section 1.1: 2D Plane Rotation & Orientation Invariance
-- ============================================================================

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

-- ============================================================================
-- Section 2: Sorting, Distinct X, Cups, and Caps
-- ============================================================================

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

/-- An ordered sequence of points forms an `a`-cup (strictly x-monotone, convex downward). -/
def IsCup (pts : List Point2D) (a : ℕ) : Prop :=
  pts.length = a ∧
  (∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1) ∧
  (∀ i (hi : i + 2 < pts.length),
    orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) > 0)

/-- An ordered sequence of points forms a `b`-cap (strictly x-monotone, convex upward). -/
def IsCap (pts : List Point2D) (b : ℕ) : Prop :=
  pts.length = b ∧
  (∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1) ∧
  (∀ i (hi : i + 2 < pts.length),
    orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) < 0)

lemma isXMonotone_get_lt_step (pts : List Point2D)
    (hx : ∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1)
    (i : ℕ) (k : ℕ) (h_ik : i + 1 + k < pts.length) :
    (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i + 1 + k, h_ik⟩).1 := by
  induction' k with k ih
  · exact hx i h_ik
  · have h_prev : i + 1 + k < pts.length := by omega
    have h1 := ih h_prev
    have h2 := hx (i + 1 + k) h_ik
    exact lt_trans h1 h2

lemma isXMonotone_get_lt (pts : List Point2D)
    (hx : ∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1)
    (i j : ℕ) (hi : i < pts.length) (hj : j < pts.length) (hij : i < j) :
    (pts.get ⟨i, hi⟩).1 < (pts.get ⟨j, hj⟩).1 := by
  have h_diff : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  rcases h_diff with ⟨k, rfl⟩
  exact isXMonotone_get_lt_step pts hx i k hj

lemma isCup_nodup (pts : List Point2D) (a : ℕ) (hcup : IsCup pts a) : pts.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  by_contra h_ne
  have h_ne_idx : i ≠ j := fun h => h_ne (Fin.ext h)
  wlog hlt : i < j generalizing i j hi hj
  · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) h_ne_idx.symm
    exact this j hj i hi heq.symm (Ne.symm h_ne) h_ne_idx.symm hgt
  have h_lt_x := isXMonotone_get_lt pts hcup.2.1 i j hi hj hlt
  have h_eq_x : (pts.get ⟨i, hi⟩).1 = (pts.get ⟨j, hj⟩).1 := by rw [heq]
  linarith

lemma isCap_nodup (pts : List Point2D) (b : ℕ) (hcap : IsCap pts b) : pts.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  by_contra h_ne
  have h_ne_idx : i ≠ j := fun h => h_ne (Fin.ext h)
  wlog hlt : i < j generalizing i j hi hj
  · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) h_ne_idx.symm
    exact this j hj i hi heq.symm (Ne.symm h_ne) h_ne_idx.symm hgt
  have h_lt_x := isXMonotone_get_lt pts hcap.2.1 i j hi hj hlt
  have h_eq_x : (pts.get ⟨i, hi⟩).1 = (pts.get ⟨j, hj⟩).1 := by rw [heq]
  linarith

lemma isCap_cons (p0 : Point2D) (pts : List Point2D) (b : ℕ) (hb : 3 ≤ b)
    (h_len : pts.length = b - 1)
    (h_x0 : 0 < pts.length → p0.1 < (pts.get ⟨0, by omega⟩).1)
    (h_x_rest : ∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1)
    (h_first : 2 ≤ pts.length → orientationDet p0 (pts.get ⟨0, by omega⟩) (pts.get ⟨1, by omega⟩) < 0)
    (h_rest : ∀ i (hi : i + 2 < pts.length),
      orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) < 0) :
    IsCap (p0 :: pts) b := by
  refine ⟨by simp [h_len]; omega, ?_, ?_⟩
  · intro i hi
    simp only [List.get_eq_getElem] at h_x_rest h_x0 ⊢
    rcases i with _ | i
    · have h0_lt : 0 < pts.length := by
        simp only [List.length_cons] at hi
        omega
      have h0 : (p0 :: pts)[0] = p0 := rfl
      have h1 : (p0 :: pts)[1] = pts[0] := rfl
      rw [h0, h1]
      exact h_x0 h0_lt
    · have hi_pts : i + 1 < pts.length := by
        simp only [List.length_cons] at hi
        omega
      have h0 : (p0 :: pts)[i + 1] = pts[i] := rfl
      have h1 : (p0 :: pts)[i + 1 + 1] = pts[i + 1] := rfl
      rw [h0, h1]
      exact h_x_rest i hi_pts
  · intro i hi
    simp only [List.get_eq_getElem] at h_rest h_first ⊢
    rcases i with _ | i
    · have h2le : 2 ≤ pts.length := by
        simp only [List.length_cons] at hi
        omega
      have h0 : (p0 :: pts)[0] = p0 := rfl
      have h1 : (p0 :: pts)[1] = pts[0] := rfl
      have h2 : (p0 :: pts)[2] = pts[1] := rfl
      rw [h0, h1, h2]
      exact h_first h2le
    · have hi_pts : i + 2 < pts.length := by
        simp only [List.length_cons] at hi
        omega
      have h0 : (p0 :: pts)[i + 1] = pts[i] := rfl
      have h1 : (p0 :: pts)[i + 1 + 1] = pts[i + 1] := rfl
      have h2 : (p0 :: pts)[i + 1 + 2] = pts[i + 2] := rfl
      rw [h0, h1, h2]
      exact h_rest i hi_pts

lemma isCup_append_one (pts : List Point2D) (q : Point2D) (a : ℕ) (ha : 4 ≤ a)
    (h_len : pts.length = a - 1)
    (h_x_cup : ∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1)
    (h_x_last : (pts.get ⟨a - 2, by omega⟩).1 < q.1)
    (h_cup : ∀ i (hi : i + 2 < pts.length),
      orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) > 0)
    (h_last : orientationDet (pts.get ⟨a - 3, by omega⟩) (pts.get ⟨a - 2, by omega⟩) q > 0) :
    IsCup (pts ++ [q]) a := by
  refine ⟨by simp [h_len]; omega, ?_, ?_⟩
  · intro i hi
    simp only [List.get_eq_getElem] at h_x_cup h_x_last ⊢
    by_cases hi_in : i + 1 < pts.length
    · have h0 : (pts ++ [q])[i] = pts[i] := List.getElem_append_left (bs := [q]) (by omega)
      have h1 : (pts ++ [q])[i + 1] = pts[i + 1] := List.getElem_append_left (bs := [q]) hi_in
      rw [h0, h1]
      exact h_x_cup i hi_in
    · have hi_eq : i = a - 2 := by
        simp only [List.length_append, List.length_singleton, h_len] at hi
        omega
      subst hi_eq
      have e0 : (pts ++ [q])[a - 2] = pts[a - 2] :=
        List.getElem_append_left (by rw [h_len]; omega)
      have e1 : (pts ++ [q])[a - 2 + 1] = q := by
        have h_le : pts.length ≤ a - 2 + 1 := by rw [h_len]; omega
        have h_lt : a - 2 + 1 - pts.length < [q].length := by simp [h_len]; omega
        have h_right : (pts ++ [q])[a - 2 + 1] = [q][a - 2 + 1 - pts.length] :=
          List.getElem_append_right h_le
        have h_zero : a - 2 + 1 - pts.length = 0 := by rw [h_len]; omega
        have h_pts : [q][a - 2 + 1 - pts.length] = [q][0] := by congr 1
        rw [h_right, h_pts]
        rfl
      rw [e0, e1]
      exact h_x_last
  · intro i hi
    simp only [List.get_eq_getElem] at h_cup h_last ⊢
    by_cases hi_in : i + 2 < pts.length
    · have h0 : (pts ++ [q])[i] = pts[i] := List.getElem_append_left (bs := [q]) (by omega)
      have h1 : (pts ++ [q])[i + 1] = pts[i + 1] := List.getElem_append_left (bs := [q]) (by omega)
      have h2 : (pts ++ [q])[i + 2] = pts[i + 2] := List.getElem_append_left (bs := [q]) hi_in
      rw [h0, h1, h2]
      exact h_cup i hi_in
    · have hi_eq : i = a - 3 := by
        simp only [List.length_append, List.length_singleton, h_len] at hi
        omega
      subst hi_eq
      have e0 : (pts ++ [q])[a - 3] = pts[a - 3] :=
        List.getElem_append_left (by rw [h_len]; omega)
      have e1 : (pts ++ [q])[a - 3 + 1] = pts[a - 2] := by
        have h : (pts ++ [q])[a - 3 + 1] = pts[a - 3 + 1] :=
          List.getElem_append_left (by rw [h_len]; omega)
        have h_idx : a - 3 + 1 = a - 2 := by omega
        have h_pts : pts[a - 3 + 1] = pts[a - 2] := by congr 1
        rw [h, h_pts]
      have e2 : (pts ++ [q])[a - 3 + 2] = q := by
        have h_le : pts.length ≤ a - 3 + 2 := by rw [h_len]; omega
        have h_lt : a - 3 + 2 - pts.length < [q].length := by simp [h_len]; omega
        have h_right : (pts ++ [q])[a - 3 + 2] = [q][a - 3 + 2 - pts.length] :=
          List.getElem_append_right h_le
        have h_zero : a - 3 + 2 - pts.length = 0 := by rw [h_len]; omega
        have h_pts : [q][a - 3 + 2 - pts.length] = [q][0] := by congr 1
        rw [h_right, h_pts]
        rfl
      rw [e0, e1, e2]
      exact h_last

lemma choose_cup_cap_split (a b : ℕ) (ha : 4 ≤ a) (hb : 4 ≤ b) :
    Nat.choose (a + b - 4) (a - 2) =
      Nat.choose (a + b - 5) (a - 3) + Nat.choose (a + b - 5) (a - 2) := by
  have h1 : a + b - 4 = (a + b - 5) + 1 := by omega
  have h2 : a - 2 = (a - 3) + 1 := by omega
  rw [h1, h2, Nat.choose_succ_succ, add_comm]

/-- Helper lemma for cup-cap theorem by strong induction on total size `s = a + b`. -/
lemma cup_cap_induction (s : ℕ) :
    ∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b) (h_sum : a + b = s)
      (S : Finset Point2D)
      (h_dist : HasDistinctX S)
      (h_card : Nat.choose (a + b - 4) (a - 2) + 1 ≤ S.card)
      (h_gen : InGeneralPosition S),
      (∃ cup : List Point2D, IsCup cup a ∧ ∀ p ∈ cup, p ∈ S) ∨
      (∃ cap : List Point2D, IsCap cap b ∧ ∀ p ∈ cap, p ∈ S) := by
  induction' s using Nat.strong_induction_on with s ih
  intro a b ha hb h_sum S h_dist h_card h_gen
  obtain ⟨L_all, hL_nodup, hL_toFinset, hL_len, hL_mono⟩ := exists_x_sorted S h_dist
  by_cases ha3 : a = 3
  · subst ha3
    have h_ch : Nat.choose (3 + b - 4) (3 - 2) + 1 = b := by
      have h1 : 3 + b - 4 = b - 1 := by omega
      have h2 : 3 - 2 = 1 := by omega
      rw [h1, h2, Nat.choose_one_right]
      omega
    have hb_card : b ≤ S.card := by rw [← h_ch]; exact h_card
    let L := L_all.take b
    have hL_sub : ∀ p ∈ L, p ∈ S := by
      intro p hp
      have := List.mem_of_mem_take hp
      have h_mem : p ∈ L_all.toFinset := List.mem_toFinset.mpr this
      rw [hL_toFinset] at h_mem
      exact h_mem
    have hL_b_len : L.length = b := by
      rw [List.length_take, hL_len]
      exact min_eq_left hb_card
    have hL_b_mono : ∀ i (hi : i + 1 < L.length), (L.get ⟨i, by omega⟩).1 < (L.get ⟨i+1, by omega⟩).1 := by
      intro i hi
      have hi_all : i + 1 < L_all.length := by rw [hL_b_len] at hi; rw [hL_len]; omega
      have e0 : L.get ⟨i, by omega⟩ = L_all.get ⟨i, by omega⟩ := by
        simp only [List.get_eq_getElem, L, List.getElem_take]
      have e1 : L.get ⟨i+1, by omega⟩ = L_all.get ⟨i+1, by omega⟩ := by
        simp only [List.get_eq_getElem, L, List.getElem_take]
      rw [e0, e1]
      exact hL_mono i hi_all
    by_cases h_pos : ∃ i, ∃ (hi : i + 2 < L.length),
        0 < orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩)
    · rcases h_pos with ⟨i, hi, h_det⟩
      let cup : List Point2D := [L.get ⟨i, by omega⟩, L.get ⟨i+1, by omega⟩, L.get ⟨i+2, by omega⟩]
      have h_cup_mono : ∀ j (hj : j + 1 < cup.length), (cup.get ⟨j, by omega⟩).1 < (cup.get ⟨j+1, by omega⟩).1 := by
        intro j hj
        have hj_lt : j < 2 := by dsimp [cup] at hj; omega
        rcases j with _ | j
        · have e0 : cup.get ⟨0, by dsimp [cup]; omega⟩ = L.get ⟨i, by omega⟩ := rfl
          have e1 : cup.get ⟨1, by dsimp [cup]; omega⟩ = L.get ⟨i+1, by omega⟩ := rfl
          rw [e0, e1]
          exact hL_b_mono i (by omega)
        · have : j = 0 := by omega
          subst this
          have e0 : cup.get ⟨1, by dsimp [cup]; omega⟩ = L.get ⟨i+1, by omega⟩ := rfl
          have e1 : cup.get ⟨2, by dsimp [cup]; omega⟩ = L.get ⟨i+2, by omega⟩ := rfl
          rw [e0, e1]
          exact hL_b_mono (i+1) hi
      refine Or.inl ⟨cup, ⟨rfl, h_cup_mono, ?_⟩, ?_⟩
      · intro j hj
        have : j = 0 := by dsimp [cup] at hj; omega
        subst this
        dsimp [cup]
        exact h_det
      · intro p hp
        dsimp [cup] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact hL_sub _ (List.get_mem ..)
        · exact hL_sub _ (List.get_mem ..)
        · exact hL_sub _ (List.get_mem ..)
    · refine Or.inr ⟨L, ⟨hL_b_len, hL_b_mono, ?_⟩, hL_sub⟩
      intro i hi
      have h_nonpos : ¬ 0 < orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) := by
        intro h
        exact h_pos ⟨i, hi, h⟩
      have h_ne : orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) ≠ 0 := by
        apply h_gen
        · exact hL_sub _ (List.get_mem ..)
        · exact hL_sub _ (List.get_mem ..)
        · exact hL_sub _ (List.get_mem ..)
        · intro heq
          have : (L.get ⟨i, by omega⟩).1 = (L.get ⟨i+1, by omega⟩).1 := by rw [heq]
          have := hL_b_mono i (by omega)
          linarith
        · intro heq
          have : (L.get ⟨i+1, by omega⟩).1 = (L.get ⟨i+2, by omega⟩).1 := by rw [heq]
          have := hL_b_mono (i+1) hi
          linarith
        · intro heq
          have : (L.get ⟨i, by omega⟩).1 = (L.get ⟨i+2, by omega⟩).1 := by rw [heq]
          have h1 := hL_b_mono i (by omega)
          have h2 := hL_b_mono (i+1) hi
          linarith
      exact lt_of_le_of_ne (le_of_not_gt h_nonpos) h_ne
  · by_cases hb3 : b = 3
    · subst hb3
      have h_ch : Nat.choose (a + 3 - 4) (a - 2) + 1 = a := by
        have h1 : a + 3 - 4 = (a - 2) + 1 := by omega
        rw [h1, Nat.choose_succ_self_right]
        omega
      have ha_card : a ≤ S.card := by rw [← h_ch]; exact h_card
      let L := L_all.take a
      have hL_sub : ∀ p ∈ L, p ∈ S := by
        intro p hp
        have := List.mem_of_mem_take hp
        have h_mem : p ∈ L_all.toFinset := List.mem_toFinset.mpr this
        rw [hL_toFinset] at h_mem
        exact h_mem
      have hL_a_len : L.length = a := by
        rw [List.length_take, hL_len]
        exact min_eq_left ha_card
      have hL_a_mono : ∀ i (hi : i + 1 < L.length), (L.get ⟨i, by omega⟩).1 < (L.get ⟨i+1, by omega⟩).1 := by
        intro i hi
        have hi_all : i + 1 < L_all.length := by rw [hL_a_len] at hi; rw [hL_len]; omega
        have e0 : L.get ⟨i, by omega⟩ = L_all.get ⟨i, by omega⟩ := by
          simp only [List.get_eq_getElem, L, List.getElem_take]
        have e1 : L.get ⟨i+1, by omega⟩ = L_all.get ⟨i+1, by omega⟩ := by
          simp only [List.get_eq_getElem, L, List.getElem_take]
        rw [e0, e1]
        exact hL_mono i hi_all
      by_cases h_neg : ∃ i, ∃ (hi : i + 2 < L.length),
          orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) < 0
      · rcases h_neg with ⟨i, hi, h_det⟩
        let cap : List Point2D := [L.get ⟨i, by omega⟩, L.get ⟨i+1, by omega⟩, L.get ⟨i+2, by omega⟩]
        have h_cap_mono : ∀ j (hj : j + 1 < cap.length), (cap.get ⟨j, by omega⟩).1 < (cap.get ⟨j+1, by omega⟩).1 := by
          intro j hj
          have hj_lt : j < 2 := by dsimp [cap] at hj; omega
          rcases j with _ | j
          · have e0 : cap.get ⟨0, by dsimp [cap]; omega⟩ = L.get ⟨i, by omega⟩ := rfl
            have e1 : cap.get ⟨1, by dsimp [cap]; omega⟩ = L.get ⟨i+1, by omega⟩ := rfl
            rw [e0, e1]
            exact hL_a_mono i (by omega)
          · have : j = 0 := by omega
            subst this
            have e0 : cap.get ⟨1, by dsimp [cap]; omega⟩ = L.get ⟨i+1, by omega⟩ := rfl
            have e1 : cap.get ⟨2, by dsimp [cap]; omega⟩ = L.get ⟨i+2, by omega⟩ := rfl
            rw [e0, e1]
            exact hL_a_mono (i+1) hi
        refine Or.inr ⟨cap, ⟨rfl, h_cap_mono, ?_⟩, ?_⟩
        · intro j hj
          have : j = 0 := by dsimp [cap] at hj; omega
          subst this
          dsimp [cap]
          exact h_det
        · intro p hp
          dsimp [cap] at hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl
          · exact hL_sub _ (List.get_mem ..)
          · exact hL_sub _ (List.get_mem ..)
          · exact hL_sub _ (List.get_mem ..)
      · refine Or.inl ⟨L, ⟨hL_a_len, hL_a_mono, ?_⟩, hL_sub⟩
        intro i hi
        have h_nonneg : ¬ orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) < 0 := by
          intro h
          exact h_neg ⟨i, hi, h⟩
        have h_ne : orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) ≠ 0 := by
          apply h_gen
          · exact hL_sub _ (List.get_mem ..)
          · exact hL_sub _ (List.get_mem ..)
          · exact hL_sub _ (List.get_mem ..)
          · intro heq
            have : (L.get ⟨i, by omega⟩).1 = (L.get ⟨i+1, by omega⟩).1 := by rw [heq]
            have := hL_a_mono i (by omega)
            linarith
          · intro heq
            have : (L.get ⟨i+1, by omega⟩).1 = (L.get ⟨i+2, by omega⟩).1 := by rw [heq]
            have := hL_a_mono (i+1) hi
            linarith
          · intro heq
            have : (L.get ⟨i, by omega⟩).1 = (L.get ⟨i+2, by omega⟩).1 := by rw [heq]
            have h1 := hL_a_mono i (by omega)
            have h2 := hL_a_mono (i+1) hi
            linarith
        exact lt_of_le_of_ne (le_of_not_gt h_nonneg) (Ne.symm h_ne)
    · have ha4 : 4 ≤ a := by omega
      have hb4 : 4 ≤ b := by omega
      let is_end (p : Point2D) : Prop :=
        ∃ c : List Point2D, IsCup c (a - 1) ∧ (∀ q ∈ c, q ∈ S) ∧ c.getLast? = some p
      haveI : DecidablePred is_end := fun p => Classical.dec (is_end p)
      let E := S.filter is_end
      by_cases h_cup_S : ∃ cup : List Point2D, IsCup cup a ∧ ∀ p ∈ cup, p ∈ S
      · exact Or.inl h_cup_S
      · have h_gen_sub : ∀ T ⊆ S, InGeneralPosition T := by
          intro T hT p q r hp hq hr hpq hqr hpr
          exact h_gen p q r (hT hp) (hT hq) (hT hr) hpq hqr hpr
        have h_dist_sub : ∀ T ⊆ S, HasDistinctX T := by
          intro T hT
          exact h_dist.subset hT
        have h_split := choose_cup_cap_split a b ha4 hb4
        let N1 := Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) + 1
        let N2 := Nat.choose (a + (b - 1) - 4) (a - 2) + 1
        have hN1_eq : N1 = Nat.choose (a + b - 5) (a - 3) + 1 := by
          have h1 : (a - 1) + b - 4 = a + b - 5 := by omega
          have h2 : (a - 1) - 2 = a - 3 := by omega
          dsimp [N1]
          rw [h1, h2]
        have hN2_eq : N2 = Nat.choose (a + b - 5) (a - 2) + 1 := by
          have h1 : a + (b - 1) - 4 = a + b - 5 := by omega
          dsimp [N2]
          rw [h1]
        have h_sum_N : Nat.choose (a + b - 4) (a - 2) + 1 = N1 + N2 - 1 := by
          rw [h_split, hN1_eq, hN2_eq]
          omega
        by_cases hN1_le : N1 ≤ (S \ E).card
        · have h_ch1 : Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) + 1 = N1 := rfl
          have h_rec := ih ((a - 1) + b) (by omega) (a - 1) b (by omega) hb (by omega) (S \ E) (h_dist_sub (S \ E) (Finset.sdiff_subset ..)) (by rw [h_ch1]; exact hN1_le) (h_gen_sub (S \ E) (Finset.sdiff_subset ..))
          rcases h_rec with ⟨c, hc_cup, hc_sub⟩ | ⟨cap, hcap, hcap_sub⟩
          · have hc_len : c.length = a - 1 := hc_cup.1
            have hc_some : ∃ p, c.getLast? = some p := by
              rcases hc : c.getLast? with _ | p
              · have := List.getLast?_eq_none_iff.mp hc
                rw [this] at hc_len
                simp at hc_len
                omega
              · exact ⟨p, rfl⟩
            obtain ⟨p, hp_last⟩ := hc_some
            obtain ⟨c_init, hc_eq⟩ := List.getLast?_eq_some_iff.mp hp_last
            have hp_in_c : p ∈ c := by rw [hc_eq]; simp
            have hp_in_sdiff : p ∈ S \ E := hc_sub p hp_in_c
            have hp_in_S : p ∈ S := (Finset.mem_sdiff.mp hp_in_sdiff).1
            have hp_not_E : p ∉ E := (Finset.mem_sdiff.mp hp_in_sdiff).2
            have hp_is_end : is_end p := ⟨c, hc_cup, fun q hq => (Finset.mem_sdiff.mp (hc_sub q hq)).1, hp_last⟩
            have hp_in_E : p ∈ E := Finset.mem_filter.mpr ⟨hp_in_S, hp_is_end⟩
            exact False.elim (hp_not_E hp_in_E)
          · refine Or.inr ⟨cap, hcap, fun p hp => (Finset.mem_sdiff.mp (hcap_sub p hp)).1⟩
        · have hN1_lt : (S \ E).card < N1 := Nat.lt_of_not_ge hN1_le
          have hE_card : N2 ≤ E.card := by
            have h_card_split : S.card = (S \ E).card + E.card := by
              have h_filt := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset is_end S)
              dsimp [E] at h_filt ⊢
              exact h_filt.symm
            rw [h_sum_N] at h_card
            omega
          have h_ch2 : Nat.choose (a + (b - 1) - 4) (a - 2) + 1 = N2 := rfl
          have h_rec := ih (a + (b - 1)) (by omega) a (b - 1) ha (by omega) (by omega) E (h_dist_sub E (Finset.filter_subset ..)) (by rw [h_ch2]; exact hE_card) (h_gen_sub E (Finset.filter_subset ..))
          rcases h_rec with ⟨cup, hcup, hcup_sub⟩ | ⟨cap, hcap, hcap_sub⟩
          · exact Or.inl ⟨cup, hcup, fun p hp => (Finset.mem_filter.mp (hcup_sub p hp)).1⟩
          · have h0_lt : 0 < cap.length := by have := hcap.1; omega
            have h1_lt : 1 < cap.length := by have := hcap.1; omega
            let e1 := cap.get ⟨0, h0_lt⟩
            let e2 := cap.get ⟨1, h1_lt⟩
            have he1_in_E : e1 ∈ E := hcap_sub e1 (List.get_mem ..)
            have he1_is_end : is_end e1 := (Finset.mem_filter.mp he1_in_E).2
            rcases he1_is_end with ⟨u, hu_cup, hu_sub, hu_last⟩
            have hu_len : u.length = a - 1 := hu_cup.1
            have ha3_lt : a - 3 < u.length := by omega
            have ha2_lt : a - 2 < u.length := by omega
            let p0 := u.get ⟨a - 3, ha3_lt⟩
            have hu_last_eq : u.get ⟨a - 2, ha2_lt⟩ = e1 := by
              have h_getElem : u[a - 2]? = some (u.get ⟨a - 2, ha2_lt⟩) := by
                rw [List.getElem?_eq_getElem (h := ha2_lt), List.get_eq_getElem]
              have h_last : u.getLast? = u[a - 2]? := by
                have : a - 2 = u.length - 1 := by omega
                rw [this, List.getLast?_eq_getElem?]
              rw [h_last, h_getElem] at hu_last
              injection hu_last
            have hp0_in_S : p0 ∈ S := hu_sub p0 (List.get_mem ..)
            have he1_lt_e2_x : e1.1 < e2.1 := hcap.2.1 0 (by rw [hcap.1]; omega)
            have hp0_lt_e1_x : p0.1 < e1.1 := by
              have h_x := hu_cup.2.1 (a - 3) (by rw [hu_len]; omega)
              have h_eq1 : u.get ⟨a - 3, by rw [hu_len]; omega⟩ = p0 := rfl
              have hu_idx : a - 3 + 1 < u.length := by rw [hu_len]; omega
              have h_eq_idx : a - 3 + 1 = a - 2 := by omega
              have h_fin : (⟨a - 3 + 1, hu_idx⟩ : Fin u.length) = ⟨a - 2, ha2_lt⟩ := Fin.ext h_eq_idx
              have h_eq2 : u.get ⟨a - 3 + 1, by rw [hu_len]; omega⟩ = e1 := by rw [h_fin, hu_last_eq]
              rw [h_eq1, h_eq2] at h_x
              exact h_x
            by_cases h_ext : 0 < orientationDet p0 e1 e2
            · have h_cup_ext : IsCup (u ++ [e2]) a := by
                apply isCup_append_one u e2 a ha4 hu_len hu_cup.2.1
                · rw [hu_last_eq]; exact he1_lt_e2_x
                · exact hu_cup.2.2
                · rw [hu_last_eq]; exact h_ext
              have h_sub_ext : ∀ q ∈ u ++ [e2], q ∈ S := by
                intro q hq
                simp only [List.mem_append, List.mem_singleton] at hq
                rcases hq with hq_u | rfl
                · exact hu_sub q hq_u
                · exact (Finset.mem_filter.mp (hcap_sub e2 (List.get_mem ..))).1
              exact Or.inl ⟨u ++ [e2], h_cup_ext, h_sub_ext⟩
            · by_cases h_det_neg : orientationDet p0 e1 e2 < 0
              · have h_cap_cons : IsCap (p0 :: cap) b :=
                  isCap_cons p0 cap b hb hcap.1 (fun _ => hp0_lt_e1_x) hcap.2.1 (fun _ => h_det_neg) hcap.2.2
                have h_sub_cons : ∀ q ∈ p0 :: cap, q ∈ S := by
                  intro q hq
                  simp only [List.mem_cons] at hq
                  rcases hq with rfl | hq_cap
                  · exact hp0_in_S
                  · exact (Finset.mem_filter.mp (hcap_sub q hq_cap)).1
                exact Or.inr ⟨p0 :: cap, h_cap_cons, h_sub_cons⟩
              · have h_zero : orientationDet p0 e1 e2 = 0 := by linarith
                have he1_ne : e1 ≠ e2 := by
                  intro heq
                  have : e1.1 = e2.1 := by rw [heq]
                  linarith
                have hp0_ne_e1 : p0 ≠ e1 := by
                  intro heq
                  have : p0.1 = e1.1 := by rw [heq]
                  linarith
                have hp0_ne_e2 : p0 ≠ e2 := by
                  intro heq
                  have : p0.1 = e2.1 := by rw [heq]
                  linarith
                have he2_in_S : e2 ∈ S := (Finset.mem_filter.mp (hcap_sub e2 (List.get_mem ..))).1
                have he1_in_S : e1 ∈ S := (Finset.mem_filter.mp he1_in_E).1
                have h_ne_zero := h_gen p0 e1 e2 hp0_in_S he1_in_S he2_in_S hp0_ne_e1 he1_ne hp0_ne_e2
                exact False.elim (h_ne_zero h_zero)

-- ============================================================================
-- Section 3: The Cup-Cap Theorem
-- ============================================================================

/-- **The Erdős–Szekeres Cup-Cap Theorem (1935).**
    Any sequence of `Nat.choose (a + b - 4) (a - 2) + 1` points sorted by x-coordinate
    in general position contains an `a`-cup or a `b`-cap. -/
theorem cup_cap_lemma (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : Nat.choose (a + b - 4) (a - 2) + 1 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    (∃ cup : List Point2D, IsCup cup a ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap b ∧ ∀ p ∈ cap, p ∈ S) := by
  exact cup_cap_induction (a + b) a b ha hb rfl S h_dist h_card h_gen

-- ============================================================================
-- Section 4: Extreme Point Hyperplane Separation for General k-Cups and k-Caps
-- ============================================================================

lemma orientationDet_four_p_r_s (p q r s : Point2D) :
    (r.1 - q.1) * orientationDet p r s =
      (r.1 - p.1) * orientationDet q r s + (s.1 - r.1) * orientationDet p q r := by
  dsimp [orientationDet]
  ring

lemma orientationDet_four_p_q_s (p q r s : Point2D) :
    (r.1 - q.1) * orientationDet p q s =
      (s.1 - q.1) * orientationDet p q r + (q.1 - p.1) * orientationDet q r s := by
  dsimp [orientationDet]
  ring

lemma orientationDet_pos_prs_of_pqr_qrs (p q r s : Point2D)
    (hpq : p.1 < q.1) (hqr : q.1 < r.1) (hrs : r.1 < s.1)
    (h_pqr : 0 < orientationDet p q r)
    (h_qrs : 0 < orientationDet q r s) :
    0 < orientationDet p r s := by
  have h_id := orientationDet_four_p_r_s p q r s
  have hrq : 0 < r.1 - q.1 := by linarith
  have hrp : 0 < r.1 - p.1 := by linarith
  have hsr : 0 < s.1 - r.1 := by linarith
  have h1 : 0 < (r.1 - p.1) * orientationDet q r s := mul_pos hrp h_qrs
  have h2 : 0 < (s.1 - r.1) * orientationDet p q r := mul_pos hsr h_pqr
  have h_sum : 0 < (r.1 - p.1) * orientationDet q r s + (s.1 - r.1) * orientationDet p q r := add_pos h1 h2
  rw [← h_id] at h_sum
  exact pos_of_mul_pos_right h_sum (le_of_lt hrq)

lemma orientationDet_pos_pqs_of_pqr_qrs (p q r s : Point2D)
    (hpq : p.1 < q.1) (hqr : q.1 < r.1) (hrs : r.1 < s.1)
    (h_pqr : 0 < orientationDet p q r)
    (h_qrs : 0 < orientationDet q r s) :
    0 < orientationDet p q s := by
  have h_id := orientationDet_four_p_q_s p q r s
  have hrq : 0 < r.1 - q.1 := by linarith
  have hsq : 0 < s.1 - q.1 := by linarith
  have hqp : 0 < q.1 - p.1 := by linarith
  have h1 : 0 < (s.1 - q.1) * orientationDet p q r := mul_pos hsq h_pqr
  have h2 : 0 < (q.1 - p.1) * orientationDet q r s := mul_pos hqp h_qrs
  have h_sum : 0 < (s.1 - q.1) * orientationDet p q r + (q.1 - p.1) * orientationDet q r s := add_pos h1 h2
  rw [← h_id] at h_sum
  exact pos_of_mul_pos_right h_sum (le_of_lt hrq)

lemma isCup_orientationDet_pos (pts : List Point2D) (a : ℕ) (hcup : IsCup pts a) :
    ∀ i j l (hi : i < pts.length) (hj : j < pts.length) (hl : l < pts.length) (hij : i < j) (hjl : j < l),
      0 < orientationDet (pts.get ⟨i, hi⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨l, hl⟩) := by
  intro i j l hi hj hl hij hjl
  have h_diff : ∃ d, l - i = d + 2 := ⟨l - i - 2, by omega⟩
  rcases h_diff with ⟨d, hd⟩
  induction' d using Nat.strong_induction_on with d ih generalizing i j l hi hj hl
  rcases eq_or_ne (i + 1) j with rfl | hj_gt
  · rcases eq_or_ne (i + 2) l with rfl | hl_gt
    · have h_det := hcup.2.2 i hl
      have h0 : (pts.get ⟨i, hi⟩) = pts.get ⟨i, by omega⟩ := by congr 1
      have h1 : (pts.get ⟨i + 1, hj⟩) = pts.get ⟨i + 1, by omega⟩ := by congr 1
      have h2 : (pts.get ⟨i + 2, hl⟩) = pts.get ⟨i + 2, by omega⟩ := by congr 1
      rw [h0, h1, h2]
      exact h_det
    · have hl_prev : i + 2 < pts.length := by omega
      have h_rec := ih (l - (i + 1) - 2) (by omega) (i + 1) (i + 2) l (by omega) (by omega) hl (by omega) (by omega) (by omega)
      have h_base := hcup.2.2 i hl_prev
      have h0 : pts.get ⟨i, by omega⟩ = pts.get ⟨i, hi⟩ := by congr 1
      have h1 : pts.get ⟨i + 1, by omega⟩ = pts.get ⟨i + 1, hj⟩ := by congr 1
      have h2 : pts.get ⟨i + 2, by omega⟩ = pts.get ⟨i + 2, hl_prev⟩ := by congr 1
      rw [h0, h1, h2] at h_base
      have hpq : (pts.get ⟨i, hi⟩).1 < (pts.get ⟨i + 1, hj⟩).1 := isXMonotone_get_lt pts hcup.2.1 i (i+1) hi hj (by omega)
      have hqr : (pts.get ⟨i + 1, hj⟩).1 < (pts.get ⟨i + 2, hl_prev⟩).1 := isXMonotone_get_lt pts hcup.2.1 (i+1) (i+2) hj hl_prev (by omega)
      have hrs : (pts.get ⟨i + 2, hl_prev⟩).1 < (pts.get ⟨l, hl⟩).1 := isXMonotone_get_lt pts hcup.2.1 (i+2) l hl_prev hl (by omega)
      exact orientationDet_pos_pqs_of_pqr_qrs (pts.get ⟨i, hi⟩) (pts.get ⟨i + 1, hj⟩) (pts.get ⟨i + 2, hl_prev⟩) (pts.get ⟨l, hl⟩) hpq hqr hrs h_base h_rec
  · have hj_prev : i + 1 < pts.length := by omega
    have h1 := ih (j - i - 2) (by omega) i (i + 1) j hi hj_prev hj (by omega) (by omega) (by omega)
    have h2 := ih (l - (i + 1) - 2) (by omega) (i + 1) j l hj_prev hj hl (by omega) hjl (by omega)
    have hpq : (pts.get ⟨i, hi⟩).1 < (pts.get ⟨i + 1, hj_prev⟩).1 := isXMonotone_get_lt pts hcup.2.1 i (i+1) hi hj_prev (by omega)
    have hqr : (pts.get ⟨i + 1, hj_prev⟩).1 < (pts.get ⟨j, hj⟩).1 := isXMonotone_get_lt pts hcup.2.1 (i+1) j hj_prev hj (by omega)
    have hrs : (pts.get ⟨j, hj⟩).1 < (pts.get ⟨l, hl⟩).1 := isXMonotone_get_lt pts hcup.2.1 j l hj hl hjl
    exact orientationDet_pos_prs_of_pqr_qrs (pts.get ⟨i, hi⟩) (pts.get ⟨i + 1, hj_prev⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨l, hl⟩) hpq hqr hrs h1 h2

/-- Any k-cup (k ≥ 3) forms the vertex set of a strictly convex k-gon. -/
lemma formsConvexPolygon_of_isCup (S : Finset Point2D) (cup : List Point2D) (k : ℕ) (hk : 3 ≤ k)
    (hcup : IsCup cup k) (h_sub : ∀ p ∈ cup, p ∈ S) :
    FormsConvexPolygon S k := by
  classical
  let poly := cup.toFinset
  have h_nodup := isCup_nodup cup k hcup
  refine ⟨poly, ?_, ?_, ?_⟩
  · intro p hp
    exact h_sub p (List.mem_toFinset.mp hp)
  · rw [List.toFinset_card_of_nodup h_nodup, hcup.1]
  · intro p hp
    have hp_mem : p ∈ cup := List.mem_toFinset.mp hp
    obtain ⟨⟨m, hm⟩, hp_eq⟩ := List.get_of_mem hp_mem
    have h_len : cup.length = k := hcup.1
    have h_set : (poly : Set Point2D) \ {p} = ↑(poly \ {p}) := by ext x; simp
    rw [h_set]
    by_cases hm0 : m = 0
    · subst hm0
      apply not_mem_convexHull_of_x_min (poly \ {p}) p
      intro t ht
      obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1)
      have hj_ne_0 : j ≠ 0 := by
        intro heq
        have h_fin : (⟨j, hj⟩ : Fin cup.length) = ⟨0, hm⟩ := Fin.ext heq
        have : cup.get ⟨j, hj⟩ = p := by rw [h_fin, hp_eq]
        exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_singleton.mpr this)
      have hj_pos : 0 < j := Nat.pos_of_ne_zero hj_ne_0
      rw [← hp_eq]
      exact isXMonotone_get_lt cup hcup.2.1 0 j hm hj hj_pos
    · by_cases hmk : m = k - 1
      · subst hmk
        apply not_mem_convexHull_of_x_max (poly \ {p}) p
        intro t ht
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1)
        have hj_ne_last : j ≠ k - 1 := by
          intro heq
          have h_fin : (⟨j, hj⟩ : Fin cup.length) = ⟨k - 1, hm⟩ := Fin.ext heq
          have : cup.get ⟨j, hj⟩ = p := by rw [h_fin, hp_eq]
          exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_singleton.mpr this)
        have hj_lt_k1 : j < k - 1 := by
          have : j < k := by rw [h_len] at hj; exact hj
          omega
        rw [← hp_eq]
        exact isXMonotone_get_lt cup hcup.2.1 j (k - 1) hj hm hj_lt_k1
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hm_lt : m < k - 1 := by
          have : m < k := by rw [h_len] at hm; exact hm
          omega
        have hm_prev_lt : m - 1 < cup.length := by rw [h_len]; omega
        have hm_next_lt : m + 1 < cup.length := by rw [h_len]; omega
        let a := cup.get ⟨m - 1, hm_prev_lt⟩
        let b := cup.get ⟨m + 1, hm_next_lt⟩
        have h_det_amb := isCup_orientationDet_pos cup k hcup (m - 1) m (m + 1) hm_prev_lt hm hm_next_lt (by omega) (by omega)
        have h_perm : orientationDet a b p = - orientationDet (cup.get ⟨m - 1, hm_prev_lt⟩) (cup.get ⟨m, hm⟩) (cup.get ⟨m + 1, hm_next_lt⟩) := by
          have hp : p = cup.get ⟨m, hm⟩ := hp_eq.symm
          rw [hp]
          exact orientationDet_perm a (cup.get ⟨m, hm⟩) b
        have hp_neg : orientationDet a b p < 0 := by linarith [h_det_amb, h_perm]
        apply not_mem_convexHull_of_separated_pos_ge (poly \ {p}) p a b hp_neg
        intro t ht
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1)
        have hj_ne_m : j ≠ m := by
          intro heq
          have h_fin : (⟨j, hj⟩ : Fin cup.length) = ⟨m, hm⟩ := Fin.ext heq
          have : cup.get ⟨j, hj⟩ = p := by rw [h_fin, hp_eq]
          exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_singleton.mpr this)
        rcases lt_trichotomy j (m - 1) with hj_lt | hj_eq_prev | hj_gt
        · have hj_pos_det := isCup_orientationDet_pos cup k hcup j (m - 1) (m + 1) hj hm_prev_lt hm_next_lt hj_lt (by omega)
          have h_cyc := orientationDet_cyclic (cup.get ⟨j, hj⟩) a b
          linarith [hj_pos_det, h_cyc]
        · have : (⟨j, hj⟩ : Fin cup.length) = ⟨m - 1, hm_prev_lt⟩ := Fin.ext hj_eq_prev
          have : cup.get ⟨j, hj⟩ = a := by rw [this]
          rw [this, orientationDet_self_right]
        · rcases eq_or_ne j (m + 1) with hj_eq_next | hj_ne_next
          · have : (⟨j, hj⟩ : Fin cup.length) = ⟨m + 1, hm_next_lt⟩ := Fin.ext hj_eq_next
            have : cup.get ⟨j, hj⟩ = b := by rw [this]
            rw [this, orientationDet_self_mid]
          · have hj_gt_next : m + 1 < j := by omega
            have hj_pos_det := isCup_orientationDet_pos cup k hcup (m - 1) (m + 1) j hm_prev_lt hm_next_lt hj (by omega) hj_gt_next
            linarith [hj_pos_det]

lemma orientationDet_neg_prs_of_pqr_qrs (p q r s : Point2D)
    (hpq : p.1 < q.1) (hqr : q.1 < r.1) (hrs : r.1 < s.1)
    (h_pqr : orientationDet p q r < 0)
    (h_qrs : orientationDet q r s < 0) :
    orientationDet p r s < 0 := by
  have h_id := orientationDet_four_p_r_s p q r s
  have hrq : 0 < r.1 - q.1 := by linarith
  have hrp : 0 < r.1 - p.1 := by linarith
  have hsr : 0 < s.1 - r.1 := by linarith
  have h1 : (r.1 - p.1) * orientationDet q r s < 0 := mul_neg_of_pos_of_neg hrp h_qrs
  have h2 : (s.1 - r.1) * orientationDet p q r < 0 := mul_neg_of_pos_of_neg hsr h_pqr
  have h_sum : (r.1 - p.1) * orientationDet q r s + (s.1 - r.1) * orientationDet p q r < 0 := by linarith
  rw [← h_id] at h_sum
  exact neg_of_mul_neg_right h_sum (le_of_lt hrq)

lemma orientationDet_neg_pqs_of_pqr_qrs (p q r s : Point2D)
    (hpq : p.1 < q.1) (hqr : q.1 < r.1) (hrs : r.1 < s.1)
    (h_pqr : orientationDet p q r < 0)
    (h_qrs : orientationDet q r s < 0) :
    orientationDet p q s < 0 := by
  have h_id := orientationDet_four_p_q_s p q r s
  have hrq : 0 < r.1 - q.1 := by linarith
  have hsq : 0 < s.1 - q.1 := by linarith
  have hqp : 0 < q.1 - p.1 := by linarith
  have h1 : (s.1 - q.1) * orientationDet p q r < 0 := mul_neg_of_pos_of_neg hsq h_pqr
  have h2 : (q.1 - p.1) * orientationDet q r s < 0 := mul_neg_of_pos_of_neg hqp h_qrs
  have h_sum : (s.1 - q.1) * orientationDet p q r + (q.1 - p.1) * orientationDet q r s < 0 := by linarith
  rw [← h_id] at h_sum
  exact neg_of_mul_neg_right h_sum (le_of_lt hrq)

lemma isCap_orientationDet_neg (pts : List Point2D) (b : ℕ) (hcap : IsCap pts b) :
    ∀ i j l (hi : i < pts.length) (hj : j < pts.length) (hl : l < pts.length) (hij : i < j) (hjl : j < l),
      orientationDet (pts.get ⟨i, hi⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨l, hl⟩) < 0 := by
  intro i j l hi hj hl hij hjl
  have h_diff : ∃ d, l - i = d + 2 := ⟨l - i - 2, by omega⟩
  rcases h_diff with ⟨d, hd⟩
  induction' d using Nat.strong_induction_on with d ih generalizing i j l hi hj hl
  rcases eq_or_ne (i + 1) j with rfl | hj_gt
  · rcases eq_or_ne (i + 2) l with rfl | hl_gt
    · have h_det := hcap.2.2 i hl
      have h0 : (pts.get ⟨i, hi⟩) = pts.get ⟨i, by omega⟩ := by congr 1
      have h1 : (pts.get ⟨i + 1, hj⟩) = pts.get ⟨i + 1, by omega⟩ := by congr 1
      have h2 : (pts.get ⟨i + 2, hl⟩) = pts.get ⟨i + 2, by omega⟩ := by congr 1
      rw [h0, h1, h2]
      exact h_det
    · have hl_prev : i + 2 < pts.length := by omega
      have h_rec := ih (l - (i + 1) - 2) (by omega) (i + 1) (i + 2) l (by omega) (by omega) hl (by omega) (by omega) (by omega)
      have h_base := hcap.2.2 i hl_prev
      have h0 : pts.get ⟨i, by omega⟩ = pts.get ⟨i, hi⟩ := by congr 1
      have h1 : pts.get ⟨i + 1, by omega⟩ = pts.get ⟨i + 1, hj⟩ := by congr 1
      have h2 : pts.get ⟨i + 2, by omega⟩ = pts.get ⟨i + 2, hl_prev⟩ := by congr 1
      rw [h0, h1, h2] at h_base
      have hpq : (pts.get ⟨i, hi⟩).1 < (pts.get ⟨i + 1, hj⟩).1 := isXMonotone_get_lt pts hcap.2.1 i (i+1) hi hj (by omega)
      have hqr : (pts.get ⟨i + 1, hj⟩).1 < (pts.get ⟨i + 2, hl_prev⟩).1 := isXMonotone_get_lt pts hcap.2.1 (i+1) (i+2) hj hl_prev (by omega)
      have hrs : (pts.get ⟨i + 2, hl_prev⟩).1 < (pts.get ⟨l, hl⟩).1 := isXMonotone_get_lt pts hcap.2.1 (i+2) l hl_prev hl (by omega)
      exact orientationDet_neg_pqs_of_pqr_qrs (pts.get ⟨i, hi⟩) (pts.get ⟨i + 1, hj⟩) (pts.get ⟨i + 2, hl_prev⟩) (pts.get ⟨l, hl⟩) hpq hqr hrs h_base h_rec
  · have hj_prev : i + 1 < pts.length := by omega
    have h1 := ih (j - i - 2) (by omega) i (i + 1) j hi hj_prev hj (by omega) (by omega) (by omega)
    have h2 := ih (l - (i + 1) - 2) (by omega) (i + 1) j l hj_prev hj hl (by omega) hjl (by omega)
    have hpq : (pts.get ⟨i, hi⟩).1 < (pts.get ⟨i + 1, hj_prev⟩).1 := isXMonotone_get_lt pts hcap.2.1 i (i+1) hi hj_prev (by omega)
    have hqr : (pts.get ⟨i + 1, hj_prev⟩).1 < (pts.get ⟨j, hj⟩).1 := isXMonotone_get_lt pts hcap.2.1 (i+1) j hj_prev hj (by omega)
    have hrs : (pts.get ⟨j, hj⟩).1 < (pts.get ⟨l, hl⟩).1 := isXMonotone_get_lt pts hcap.2.1 j l hj hl hjl
    exact orientationDet_neg_prs_of_pqr_qrs (pts.get ⟨i, hi⟩) (pts.get ⟨i + 1, hj_prev⟩) (pts.get ⟨j, hj⟩) (pts.get ⟨l, hl⟩) hpq hqr hrs h1 h2

/-- Any k-cap (k ≥ 3) forms the vertex set of a strictly convex k-gon. -/
lemma formsConvexPolygon_of_isCap (S : Finset Point2D) (cap : List Point2D) (k : ℕ) (hk : 3 ≤ k)
    (hcap : IsCap cap k) (h_sub : ∀ p ∈ cap, p ∈ S) :
    FormsConvexPolygon S k := by
  classical
  let poly := cap.toFinset
  have h_nodup := isCap_nodup cap k hcap
  refine ⟨poly, ?_, ?_, ?_⟩
  · intro p hp
    exact h_sub p (List.mem_toFinset.mp hp)
  · rw [List.toFinset_card_of_nodup h_nodup, hcap.1]
  · intro p hp
    have hp_mem : p ∈ cap := List.mem_toFinset.mp hp
    obtain ⟨⟨m, hm⟩, hp_eq⟩ := List.get_of_mem hp_mem
    have h_len : cap.length = k := hcap.1
    have h_set : (poly : Set Point2D) \ {p} = ↑(poly \ {p}) := by ext x; simp
    rw [h_set]
    by_cases hm0 : m = 0
    · subst hm0
      apply not_mem_convexHull_of_x_min (poly \ {p}) p
      intro t ht
      obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1)
      have hj_ne_0 : j ≠ 0 := by
        intro heq
        have h_fin : (⟨j, hj⟩ : Fin cap.length) = ⟨0, hm⟩ := Fin.ext heq
        have : cap.get ⟨j, hj⟩ = p := by rw [h_fin, hp_eq]
        exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_singleton.mpr this)
      have hj_pos : 0 < j := Nat.pos_of_ne_zero hj_ne_0
      rw [← hp_eq]
      exact isXMonotone_get_lt cap hcap.2.1 0 j hm hj hj_pos
    · by_cases hmk : m = k - 1
      · subst hmk
        apply not_mem_convexHull_of_x_max (poly \ {p}) p
        intro t ht
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1)
        have hj_ne_last : j ≠ k - 1 := by
          intro heq
          have h_fin : (⟨j, hj⟩ : Fin cap.length) = ⟨k - 1, hm⟩ := Fin.ext heq
          have : cap.get ⟨j, hj⟩ = p := by rw [h_fin, hp_eq]
          exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_singleton.mpr this)
        have hj_lt_k1 : j < k - 1 := by
          have : j < k := by rw [h_len] at hj; exact hj
          omega
        rw [← hp_eq]
        exact isXMonotone_get_lt cap hcap.2.1 j (k - 1) hj hm hj_lt_k1
      · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
        have hm_lt : m < k - 1 := by
          have : m < k := by rw [h_len] at hm; exact hm
          omega
        have hm_prev_lt : m - 1 < cap.length := by rw [h_len]; omega
        have hm_next_lt : m + 1 < cap.length := by rw [h_len]; omega
        let a := cap.get ⟨m - 1, hm_prev_lt⟩
        let b := cap.get ⟨m + 1, hm_next_lt⟩
        have h_det_amb := isCap_orientationDet_neg cap k hcap (m - 1) m (m + 1) hm_prev_lt hm hm_next_lt (by omega) (by omega)
        have h_perm : orientationDet a b p = - orientationDet (cap.get ⟨m - 1, hm_prev_lt⟩) (cap.get ⟨m, hm⟩) (cap.get ⟨m + 1, hm_next_lt⟩) := by
          have hp : p = cap.get ⟨m, hm⟩ := hp_eq.symm
          rw [hp]
          exact orientationDet_perm a (cap.get ⟨m, hm⟩) b
        have hp_pos : 0 < orientationDet a b p := by linarith [h_det_amb, h_perm]
        apply not_mem_convexHull_of_separated_neg_le (poly \ {p}) p a b hp_pos
        intro t ht
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem (List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1)
        have hj_ne_m : j ≠ m := by
          intro heq
          have h_fin : (⟨j, hj⟩ : Fin cap.length) = ⟨m, hm⟩ := Fin.ext heq
          have : cap.get ⟨j, hj⟩ = p := by rw [h_fin, hp_eq]
          exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_singleton.mpr this)
        rcases lt_trichotomy j (m - 1) with hj_lt | hj_eq_prev | hj_gt
        · have hj_neg_det := isCap_orientationDet_neg cap k hcap j (m - 1) (m + 1) hj hm_prev_lt hm_next_lt hj_lt (by omega)
          have h_cyc := orientationDet_cyclic (cap.get ⟨j, hj⟩) a b
          linarith [hj_neg_det, h_cyc]
        · have : (⟨j, hj⟩ : Fin cap.length) = ⟨m - 1, hm_prev_lt⟩ := Fin.ext hj_eq_prev
          have : cap.get ⟨j, hj⟩ = a := by rw [this]
          rw [this, orientationDet_self_right]
        · rcases eq_or_ne j (m + 1) with hj_eq_next | hj_ne_next
          · have : (⟨j, hj⟩ : Fin cap.length) = ⟨m + 1, hm_next_lt⟩ := Fin.ext hj_eq_next
            have : cap.get ⟨j, hj⟩ = b := by rw [this]
            rw [this, orientationDet_self_mid]
          · have hj_gt_next : m + 1 < j := by omega
            have hj_neg_det := isCap_orientationDet_neg cap k hcap (m - 1) (m + 1) j hm_prev_lt hm_next_lt hj (by omega) hj_gt_next
            linarith [hj_neg_det]

-- ============================================================================
-- Section 5: The Erdős–Szekeres Theorem & Corollaries
-- ============================================================================

/-- The Erdős–Szekeres upper bound: ES(k) ≤ Nat.choose (2*k - 4) (k - 2) + 1. -/
def erdosSzekeresBound (k : ℕ) : ℕ :=
  Nat.choose (2 * k - 4) (k - 2) + 1

/-- **Main Theorem: Erdős–Szekeres Convex Polygon Theorem (1935).**
    Every set of at least `erdosSzekeresBound k` points in general position with distinct x-coordinates
    contains the vertices of a strictly convex k-gon (`FormsConvexPolygon S k`). -/
theorem erdos_szekeres_convex_polygon (k : ℕ) (hk : 3 ≤ k)
    (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : erdosSzekeresBound k ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S k := by
  have h_bound : Nat.choose (k + k - 4) (k - 2) + 1 ≤ S.card := by
    have : k + k = 2 * k := by omega
    rw [this]
    exact h_card
  have h_cup_cap := cup_cap_lemma k k hk hk S h_dist h_bound h_gen
  rcases h_cup_cap with ⟨cup, hcup, hcup_sub⟩ | ⟨cap, hcap, hcap_sub⟩
  · exact formsConvexPolygon_of_isCup S cup k hk hcup hcup_sub
  · exact formsConvexPolygon_of_isCap S cap k hk hcap hcap_sub

/-- For k = 3, every set of at least 3 points in general position with distinct x-coordinates
    contains a convex triangle. Exact evaluation: ES(3) = 3. -/
theorem erdos_szekeres_triangle (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : 3 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S 3 := by
  have h_bound : erdosSzekeresBound 3 ≤ S.card := by
    dsimp [erdosSzekeresBound]
    exact h_card
  exact erdos_szekeres_convex_polygon 3 (by omega) S h_dist h_bound h_gen

/-- For k = 4, every set of at least 7 points in general position with distinct x-coordinates
    contains a convex quadrilateral (general upper bound `ES(4) ≤ 7`). -/
theorem erdos_szekeres_four_points (S : Finset Point2D)
    (h_dist : HasDistinctX S)
    (h_card : 7 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    FormsConvexPolygon S 4 := by
  have h_bound : erdosSzekeresBound 4 ≤ S.card := by
    dsimp [erdosSzekeresBound]
    exact h_card
  exact erdos_szekeres_convex_polygon 4 (by omega) S h_dist h_bound h_gen

/-- The Erdős–Szekeres Exact Conjecture: ES(k) = 2^(k-2) + 1 for all k ≥ 3.
    Proven for k = 3 (ES=3), k = 4 (ES=5, Esther Klein), k = 5 (ES=9, Kalbfleisch et al.),
    and k = 6 (ES=17, Szekeres–Peters 2006). Open for k ≥ 7. -/
def ErdosSzekeresConjecture : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (S : Finset Point2D),
    HasDistinctX S →
    2^(k - 2) + 1 ≤ S.card →
    InGeneralPosition S →
    FormsConvexPolygon S k
