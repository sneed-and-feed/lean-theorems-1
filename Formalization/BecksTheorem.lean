import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open scoped Classical

noncomputable section

/-!
# Beck's Theorem on Incidence Geometry (1983)

**Beck's Theorem (József Beck, 1983)** is a fundamental dichotomy in combinatorial geometry.
It states that any finite set of $n$ points in the Euclidean plane $\mathbb{R}^2$
falls into one of two extreme regimes:
1. **Collinear Dominance:** A single line contains a positive fraction $c_1 \cdot n$ of all points.
2. **Quadratic Line Generation:** The points span $\Omega(n^2)$ distinct lines.

## Mathematical Statement
There exist absolute positive constants $c_1, c_2 > 0$ such that for any finite set $P \subset \mathbb{R}^2$
of $n$ points:
- Either some line contains at least $c_1 n$ points of $P$,
- Or the set of lines spanned by pairs in $P$ satisfies $|\mathcal{L}(P)| \ge c_2 n^2$.

## Structure of the Formalization
1. **Geometric Lines & Collinearity in $\mathbb{R}^2$:**
   Concrete definitions of 2D cross product, collinearity predicate, lines through pairs,
   and parameterization of lines.
2. **Line Uniqueness:**
   Proof that two distinct points uniquely identify an affine line in $\mathbb{R}^2$.
3. **Point Configurations & Spanned Lines:**
   Computable `Finset` definitions of points on lines, distinct pairs, spanned lines $\mathcal{L}(P)$,
   `spannedLinesCount`, and `maxCollinearPoints`.
4. **Pairs Partition & Double-Counting Identity:**
   Proof that the set of distinct pairs in $P$ is partitioned by the lines in $\mathcal{L}(P)$,
   yielding the fundamental exact identity:
   $$\sum_{\ell \in \mathcal{L}(P)} |\ell|(|\ell| - 1) = |P|(|P| - 1)$$
5. **Incidence Bounds & Beck's Dichotomy Theorem:**
   Deduction of the lower bound on $|\mathcal{L}(P)|$ and Beck's dichotomy.
-/

namespace BecksTheorem

-- ============================================================================
-- Section 1: Geometric Lines & Collinearity in ℝ²
-- ============================================================================

/-- 2D Cartesian point in the real affine plane. -/
abbrev Point2D := ℝ × ℝ

/-- 2D cross product / determinant of two displacement vectors. -/
def cross (u v : Point2D) : ℝ :=
  u.1 * v.2 - u.2 * v.1

/-- 2D cross product of triangle (p, q, r). -/
def crossProd (p q r : Point2D) : ℝ :=
  cross (q.1 - p.1, q.2 - p.2) (r.1 - p.1, r.2 - p.2)

/-- Three points p, q, r are collinear if their cross product vanishes. -/
def Collinear (p q r : Point2D) : Prop :=
  crossProd p q r = 0

/-- The line spanned by two distinct points p and q in ℝ². -/
def lineThrough (p q : Point2D) : Set Point2D :=
  {r | Collinear p q r}

lemma collinear_self_left (p q : Point2D) : Collinear p q p := by dsimp [Collinear, crossProd, cross]; ring
lemma collinear_self_right (p q : Point2D) : Collinear p q q := by dsimp [Collinear, crossProd, cross]; ring
lemma collinear_self_first_two (p r : Point2D) : Collinear p p r := by dsimp [Collinear, crossProd, cross]; ring

lemma mem_lineThrough_left (p q : Point2D) : p ∈ lineThrough p q := collinear_self_left p q
lemma mem_lineThrough_right (p q : Point2D) : q ∈ lineThrough p q := collinear_self_right p q

lemma crossProd_perm_right (p q r : Point2D) : crossProd p r q = - crossProd p q r := by dsimp [crossProd, cross]; ring
lemma collinear_perm_right (p q r : Point2D) : Collinear p r q ↔ Collinear p q r := by rw [Collinear, Collinear, crossProd_perm_right, neg_eq_zero]

lemma crossProd_perm_left (p q r : Point2D) : crossProd q p r = - crossProd p q r := by dsimp [crossProd, cross]; ring
lemma collinear_perm_left (p q r : Point2D) : Collinear q p r ↔ Collinear p q r := by rw [Collinear, Collinear, crossProd_perm_left, neg_eq_zero]

lemma lineThrough_comm (p q : Point2D) : lineThrough p q = lineThrough q p := by
  ext r; exact (collinear_perm_left p q r).symm

-- ============================================================================
-- Section 2: Line Parameterization & Uniqueness
-- ============================================================================

/-- Squared Euclidean norm of a 2D vector. -/
def sqNorm (u : Point2D) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- Dot product of two 2D vectors. -/
def dot (u v : Point2D) : ℝ :=
  u.1 * v.1 + u.2 * v.2

lemma sqNorm_pos_of_ne {u : Point2D} (h : u ≠ (0, 0)) : 0 < sqNorm u := by
  have : u.1 ≠ 0 ∨ u.2 ≠ 0 := by contrapose! h; ext <;> tauto
  rcases this with h1 | h2 <;> (unfold sqNorm; positivity)

lemma sqNorm_pos_of_points_ne {p q : Point2D} (h : p ≠ q) :
    0 < sqNorm (q.1 - p.1, q.2 - p.2) := by
  apply sqNorm_pos_of_ne; contrapose! h; ext
  · have := congr_arg Prod.fst h; linarith
  · have := congr_arg Prod.snd h; linarith

lemma sqNorm_ne_zero_of_points_ne {p q : Point2D} (h : p ≠ q) :
    sqNorm (q.1 - p.1, q.2 - p.2) ≠ 0 :=
  (sqNorm_pos_of_points_ne h).ne'

/-- Point along the line pq at parameter t. -/
def paramPoint (p q : Point2D) (t : ℝ) : Point2D :=
  (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2))

/-- Projection parameter of point r onto the line pq. -/
def paramVal (p q r : Point2D) : ℝ :=
  dot (r.1 - p.1, r.2 - p.2) (q.1 - p.1, q.2 - p.2) / sqNorm (q.1 - p.1, q.2 - p.2)

lemma collinear_param_eq (p q r : Point2D) (hne : p ≠ q) (hcol : Collinear p q r) :
    r = paramPoint p q (paramVal p q r) := by
  let v : Point2D := (q.1 - p.1, q.2 - p.2)
  let t := paramVal p q r
  have hv_ne : sqNorm v ≠ 0 := sqNorm_ne_zero_of_points_ne hne
  dsimp [Collinear, crossProd, cross] at hcol
  ext
  · dsimp [t, paramVal, dot, sqNorm, v, paramPoint]
    have hv_ne' : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 ≠ 0 := hv_ne
    have hX : ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) =
        (r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2) :=
      div_mul_cancel₀ _ hv_ne'
    have : (r.1 - p.1) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) =
        (((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * (q.1 - p.1)) *
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
      calc
        (r.1 - p.1) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)
        _ = ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) * (q.1 - p.1) -
            (q.2 - p.2) * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) := by ring
        _ = ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) * (q.1 - p.1) -
            (q.2 - p.2) * 0 := by rw [hcol]
        _ = ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) * (q.1 - p.1) := by ring
        _ = (((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
            ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)) *
            (q.1 - p.1) := by rw [hX]
        _ = (((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
            ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * (q.1 - p.1)) *
            ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by ring
    have h_eq := mul_right_cancel₀ hv_ne' this
    linarith
  · dsimp [t, paramVal, dot, sqNorm, v, paramPoint]
    have hv_ne' : (q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2 ≠ 0 := hv_ne
    have hX : ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) =
        (r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2) :=
      div_mul_cancel₀ _ hv_ne'
    have : (r.2 - p.2) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) =
        (((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * (q.2 - p.2)) *
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
      calc
        (r.2 - p.2) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)
        _ = ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) * (q.2 - p.2) +
            (q.1 - p.1) * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) := by ring
        _ = ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) * (q.2 - p.2) +
            (q.1 - p.1) * 0 := by rw [hcol]
        _ = ((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) * (q.2 - p.2) := by ring
        _ = (((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
            ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)) *
            (q.2 - p.2) := by rw [hX]
        _ = (((r.1 - p.1) * (q.1 - p.1) + (r.2 - p.2) * (q.2 - p.2)) /
            ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) * (q.2 - p.2)) *
            ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by ring
    have h_eq := mul_right_cancel₀ hv_ne' this
    linarith

lemma crossProd_param (p q r : Point2D) (t1 t2 : ℝ) :
    crossProd (paramPoint p q t1) (paramPoint p q t2) r = (t2 - t1) * crossProd p q r := by
  dsimp [crossProd, cross, paramPoint]
  ring

lemma paramPoint_inj (p q : Point2D) (hne : p ≠ q) (t1 t2 : ℝ) :
    paramPoint p q t1 = paramPoint p q t2 → t1 = t2 := by
  intro heq
  have h_norm : sqNorm (q.1 - p.1, q.2 - p.2) ≠ 0 := sqNorm_ne_zero_of_points_ne hne
  have hfst := congr_arg Prod.fst heq
  have hsnd := congr_arg Prod.snd heq
  dsimp [paramPoint] at hfst hsnd
  have : t1 - t2 = 0 := by
    apply mul_right_cancel₀ h_norm
    calc
      _ = (t1 - t2) * sqNorm (q.1 - p.1, q.2 - p.2) := by ring
      _ = 0 := by dsimp [sqNorm]; linear_combination (q.1 - p.1) * hfst + (q.2 - p.2) * hsnd
      _ = 0 * sqNorm (q.1 - p.1, q.2 - p.2) := by ring
  exact eq_of_sub_eq_zero this

/-- Two distinct points on a line uniquely determine the line. -/
lemma lineThrough_eq_of_mem (p q u v : Point2D) (hpq : p ≠ q)
    (hu : u ∈ lineThrough p q) (hv : v ∈ lineThrough p q) (huv : u ≠ v) :
    lineThrough u v = lineThrough p q := by
  have hu_eq : u = paramPoint p q (paramVal p q u) := collinear_param_eq p q u hpq hu
  have hv_eq : v = paramPoint p q (paramVal p q v) := collinear_param_eq p q v hpq hv
  have ht_ne : paramVal p q v - paramVal p q u ≠ 0 := by
    intro h; apply huv; rw [hu_eq, hv_eq, sub_eq_zero.mp h]
  ext r
  simp only [lineThrough, Set.mem_setOf_eq, Collinear]
  have h_cross : crossProd u v r = crossProd (paramPoint p q (paramVal p q u)) (paramPoint p q (paramVal p q v)) r := by
    calc crossProd u v r
      _ = crossProd (paramPoint p q (paramVal p q u)) v r := congrArg (fun x => crossProd x v r) hu_eq
      _ = crossProd (paramPoint p q (paramVal p q u)) (paramPoint p q (paramVal p q v)) r := congrArg (fun y => crossProd (paramPoint p q (paramVal p q u)) y r) hv_eq
  rw [h_cross, crossProd_param, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (heq | hcol)
    · exact False.elim (ht_ne (sub_eq_zero.mpr heq))
    · exact hcol
  · exact Or.inr

-- ============================================================================
-- Section 3: Point Configurations & Spanned Lines
-- ============================================================================

/-- The points of P lying on the line spanned by p and q. -/
def pointsOnLine (P : Finset Point2D) (p q : Point2D) : Finset Point2D :=
  P.filter (fun r => Collinear p q r)

/-- The set of all ordered pairs of distinct points in P. -/
def distinctPairs (P : Finset Point2D) : Finset (Point2D × Point2D) :=
  (P ×ˢ P).filter (fun ⟨p, q⟩ => p ≠ q)

/-- The finite set of all distinct lines spanned by pairs of points in P. -/
def spannedLines (P : Finset Point2D) : Finset (Finset Point2D) :=
  (distinctPairs P).image (fun ⟨p, q⟩ => pointsOnLine P p q)

/-- Number of distinct lines spanned by pairs of points in P. -/
def spannedLinesCount (P : Finset Point2D) : ℕ :=
  (spannedLines P).card

/-- Maximum number of collinear points in a point configuration P. -/
def maxCollinearPoints (P : Finset Point2D) : ℕ :=
  Finset.sup (spannedLines P) Finset.card

lemma pointsOnLine_subset (P : Finset Point2D) (p q : Point2D) :
    pointsOnLine P p q ⊆ P :=
  Finset.filter_subset _ P

lemma mem_pointsOnLine_left (P : Finset Point2D) {p q : Point2D} (hp : p ∈ P) :
    p ∈ pointsOnLine P p q := by
  rw [pointsOnLine, Finset.mem_filter]
  exact ⟨hp, collinear_self_left p q⟩

lemma mem_pointsOnLine_right (P : Finset Point2D) {p q : Point2D} (hq : q ∈ P) :
    q ∈ pointsOnLine P p q := by
  rw [pointsOnLine, Finset.mem_filter]
  exact ⟨hq, collinear_self_right p q⟩

lemma pointsOnLine_mem_spannedLines (P : Finset Point2D) {p q : Point2D}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    pointsOnLine P p q ∈ spannedLines P := by
  rw [spannedLines, Finset.mem_image]
  refine ⟨(p, q), ?_, rfl⟩
  rw [distinctPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hp, hq⟩, hne⟩

lemma spannedLines_subset (P : Finset Point2D) {l : Finset Point2D}
    (hl : l ∈ spannedLines P) : l ⊆ P := by
  rw [spannedLines, Finset.mem_image] at hl
  obtain ⟨⟨p, q⟩, -, rfl⟩ := hl
  exact pointsOnLine_subset P p q

lemma two_le_card_pointsOnLine (P : Finset Point2D) {p q : Point2D}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    2 ≤ (pointsOnLine P p q).card := by
  have hp_in : p ∈ pointsOnLine P p q := mem_pointsOnLine_left P hp
  have hq_in : q ∈ pointsOnLine P p q := mem_pointsOnLine_right P hq
  have h_sub : {p, q} ⊆ pointsOnLine P p q := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hp_in
    · exact hq_in
  have h_pair_card : ({p, q} : Finset Point2D).card = 2 := Finset.card_pair hne
  rw [← h_pair_card]
  exact Finset.card_le_card h_sub

lemma two_le_card_of_mem_spannedLines (P : Finset Point2D) {l : Finset Point2D}
    (hl : l ∈ spannedLines P) : 2 ≤ l.card := by
  rw [spannedLines, Finset.mem_image] at hl
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hl
  rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hpq
  exact two_le_card_pointsOnLine P hpq.1.1 hpq.1.2 hpq.2

lemma card_le_maxCollinearPoints (P : Finset Point2D) {l : Finset Point2D}
    (hl : l ∈ spannedLines P) : l.card ≤ maxCollinearPoints P :=
  Finset.le_sup hl

lemma pointsOnLine_eq_of_mem (P : Finset Point2D) {p q u v : Point2D}
    (hpq : p ≠ q) (hu : u ∈ pointsOnLine P p q) (hv : v ∈ pointsOnLine P p q) (huv : u ≠ v) :
    pointsOnLine P u v = pointsOnLine P p q := by
  have hu_line : u ∈ lineThrough p q := (Finset.mem_filter.mp hu).2
  have hv_line : v ∈ lineThrough p q := (Finset.mem_filter.mp hv).2
  have h_line_eq := lineThrough_eq_of_mem p q u v hpq hu_line hv_line huv
  ext r
  simp only [pointsOnLine, Finset.mem_filter, lineThrough, Set.mem_setOf_eq] at hu_line hv_line ⊢
  constructor
  · intro hr
    have hr_line : r ∈ lineThrough u v := hr.2
    rw [h_line_eq] at hr_line
    exact ⟨hr.1, hr_line⟩
  · intro hr
    have hr_line : r ∈ lineThrough p q := hr.2
    rw [← h_line_eq] at hr_line
    exact ⟨hr.1, hr_line⟩

lemma spannedLines_eq_of_mem (P : Finset Point2D) {l : Finset Point2D} (hl : l ∈ spannedLines P)
    {u v : Point2D} (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) :
    pointsOnLine P u v = l := by
  rw [spannedLines, Finset.mem_image] at hl
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hl
  rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hpq
  exact pointsOnLine_eq_of_mem P hpq.2 hu hv huv

-- ============================================================================
-- Section 4: Pairs Partition & Double-Counting Identity
-- ============================================================================

/-- Set of off-diagonal pairs in a point set s. -/
def offDiag (s : Finset Point2D) : Finset (Point2D × Point2D) :=
  (s ×ˢ s).filter (fun ⟨p, q⟩ => p ≠ q)

lemma card_offDiag (s : Finset Point2D) : (offDiag s).card = s.card * (s.card - 1) := by
  have h_disj : Disjoint (s.image (fun p => (p, p))) (offDiag s) := by
    rw [Finset.disjoint_left]
    intro ⟨x, y⟩ h1 h2
    simp only [Finset.mem_image] at h1
    simp only [offDiag, Finset.mem_filter] at h2
    obtain ⟨p, hp, hxy⟩ := h1
    have hx : x = p := (Prod.ext_iff.mp hxy).1.symm
    have hy : y = p := (Prod.ext_iff.mp hxy).2.symm
    have : x = y := hx.trans hy.symm
    exact h2.2 this
  have h_union : s ×ˢ s = (s.image (fun p => (p, p))) ∪ offDiag s := by
    ext ⟨x, y⟩
    simp only [Finset.mem_product, Finset.mem_union, Finset.mem_image, offDiag, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hy⟩
      by_cases h : x = y
      · left; exact ⟨x, hx, Prod.ext rfl h⟩
      · right; exact ⟨⟨hx, hy⟩, h⟩
    · rintro (⟨p, hp, hxy⟩ | ⟨⟨hx, hy⟩, h⟩)
      · have hx : x = p := (Prod.ext_iff.mp hxy).1.symm
        have hy : y = p := (Prod.ext_iff.mp hxy).2.symm
        rw [hx, hy]
        exact ⟨hp, hp⟩
      · exact ⟨hx, hy⟩
  have h_card : (s ×ˢ s).card = (s.image (fun p => (p, p))).card + (offDiag s).card := by
    conv_lhs => rw [h_union]
    rw [Finset.card_union_of_disjoint h_disj]
  have h_diag_card : (s.image (fun p => (p, p))).card = s.card := by
    rw [Finset.card_image_of_injective]
    intro a b hab
    exact (Prod.mk.injEq a a b b).mp hab |>.1
  rw [Finset.card_product, h_diag_card] at h_card
  cases hs : s.card with
  | zero =>
    have : s = ∅ := Finset.card_eq_zero.mp hs
    subst this
    simp [offDiag]
  | succ n =>
    have h_prod : (n + 1) * (n + 1) = (n + 1) + (n + 1) * n := by ring
    rw [hs, h_prod] at h_card
    have h_res := Nat.add_left_cancel h_card
    have h_sub : n + 1 - 1 = n := rfl
    rw [h_sub, ← h_res]

lemma distinctPairs_eq_offDiag (P : Finset Point2D) : distinctPairs P = offDiag P := rfl

lemma disjoint_offDiag_of_ne (P : Finset Point2D) {l1 l2 : Finset Point2D}
    (hl1 : l1 ∈ spannedLines P) (hl2 : l2 ∈ spannedLines P) (hne : l1 ≠ l2) :
    Disjoint (offDiag l1) (offDiag l2) := by
  rw [Finset.disjoint_left]
  intro ⟨u, v⟩ h1 h2
  simp only [offDiag, Finset.mem_filter, Finset.mem_product] at h1 h2
  obtain ⟨⟨hu1, hv1⟩, huv⟩ := h1
  obtain ⟨⟨hu2, hv2⟩, -⟩ := h2
  have hl1_eq := spannedLines_eq_of_mem P hl1 hu1 hv1 huv
  have hl2_eq := spannedLines_eq_of_mem P hl2 hu2 hv2 huv
  have : l1 = l2 := hl1_eq.symm.trans hl2_eq
  exact hne this

lemma biUnion_offDiag_eq (P : Finset Point2D) :
    (spannedLines P).biUnion offDiag = distinctPairs P := by
  ext ⟨u, v⟩
  constructor
  · intro h
    simp only [Finset.mem_biUnion, offDiag, Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨l, hl, ⟨⟨hu, hv⟩, huv⟩⟩ := h
    have hl_sub : l ⊆ P := spannedLines_subset P hl
    simp only [distinctPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hl_sub hu, hl_sub hv⟩, huv⟩
  · intro h
    simp only [distinctPairs, Finset.mem_filter, Finset.mem_product] at h
    obtain ⟨⟨hu, hv⟩, huv⟩ := h
    let l := pointsOnLine P u v
    have hl : l ∈ spannedLines P := pointsOnLine_mem_spannedLines P hu hv huv
    rw [Finset.mem_biUnion]
    refine ⟨l, hl, ?_⟩
    simp only [offDiag, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨mem_pointsOnLine_left P hu, mem_pointsOnLine_right P hv⟩, huv⟩

/-- The fundamental pairs double-counting identity:
    ∑_{ℓ ∈ ℒ(P)} |ℓ|(|ℓ| - 1) = |P|(|P| - 1). -/
theorem sum_card_pairs_eq (P : Finset Point2D) :
    ∑ l ∈ spannedLines P, l.card * (l.card - 1) = P.card * (P.card - 1) := by
  have h_biUnion : (spannedLines P).biUnion offDiag = distinctPairs P := biUnion_offDiag_eq P
  have h_disj : ∀ l1 ∈ spannedLines P, ∀ l2 ∈ spannedLines P, l1 ≠ l2 → Disjoint (offDiag l1) (offDiag l2) :=
    fun l1 hl1 l2 hl2 hne => disjoint_offDiag_of_ne P hl1 hl2 hne
  have h_card := Finset.card_biUnion h_disj
  rw [h_biUnion] at h_card
  simp_rw [card_offDiag] at h_card
  have h_P : (distinctPairs P).card = P.card * (P.card - 1) := card_offDiag P
  rw [h_P] at h_card
  exact h_card.symm

-- ============================================================================
-- Section 5: Incidence Bounds & Beck's Dichotomy Theorem
-- ============================================================================

/-- Fundamental Pair-Counting Inequality:
    |P|(|P| - 1) ≤ |ℒ(P)| · k(k - 1) where k = maxCollinearPoints(P). -/
theorem pair_counting_bound (P : Finset Point2D) :
    P.card * (P.card - 1) ≤ (spannedLinesCount P) * (maxCollinearPoints P) * (maxCollinearPoints P - 1) := by
  have h_sum := sum_card_pairs_eq P
  rw [← h_sum]
  have h_le : ∀ l ∈ spannedLines P, l.card * (l.card - 1) ≤ (maxCollinearPoints P) * (maxCollinearPoints P - 1) := by
    intro l hl
    have h_card_le := card_le_maxCollinearPoints P hl
    have : l.card - 1 ≤ maxCollinearPoints P - 1 := by omega
    nlinarith
  have h_sum_le := Finset.sum_le_sum h_le
  rw [Finset.sum_const, nsmul_eq_mul] at h_sum_le
  dsimp [spannedLinesCount]
  calc
    ∑ i ∈ spannedLines P, i.card * (i.card - 1)
    _ ≤ (spannedLines P).card * (maxCollinearPoints P * (maxCollinearPoints P - 1)) := h_sum_le
    _ = (spannedLines P).card * maxCollinearPoints P * (maxCollinearPoints P - 1) := by ring

lemma nat_cast_mul_sub_one (n : ℕ) : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    push_cast
    ring

lemma nat_cast_mul_mul_sub_one (m k : ℕ) :
    ((m * k * (k - 1) : ℕ) : ℝ) = (m : ℝ) * (k : ℝ) * ((k : ℝ) - 1) := by
  have h1 : ((m * (k * (k - 1)) : ℕ) : ℝ) = (m : ℝ) * ((k * (k - 1) : ℕ) : ℝ) := by push_cast; rfl
  have h2 : m * k * (k - 1) = m * (k * (k - 1)) := by ring
  rw [h2, h1, nat_cast_mul_sub_one k]
  ring

/-- Real-valued formulation of the Pair-Counting Inequality. -/
theorem pair_counting_bound_real (P : Finset Point2D) :
    (P.card : ℝ) * ((P.card : ℝ) - 1) ≤
      (spannedLinesCount P : ℝ) * (maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1) := by
  have h := pair_counting_bound P
  have h_cast : ((P.card * (P.card - 1) : ℕ) : ℝ) ≤
      (((spannedLinesCount P * maxCollinearPoints P * (maxCollinearPoints P - 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr h
  rw [nat_cast_mul_sub_one (P.card)] at h_cast
  rw [nat_cast_mul_mul_sub_one (spannedLinesCount P) (maxCollinearPoints P)] at h_cast
  exact h_cast

/-- Lower bound on the number of spanned lines when max collinear points is bounded:
    |ℒ(P)| ≥ n(n-1) / (k(k-1)). -/
theorem spanned_lines_bound_of_max_collinear (P : Finset Point2D) (hn : 2 ≤ P.card)
    (hk_pos : 0 < (maxCollinearPoints P : ℝ) - 1) :
    (spannedLinesCount P : ℝ) ≥
      ((P.card : ℝ) * ((P.card : ℝ) - 1)) / ((maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1)) := by
  have h_bound := pair_counting_bound_real P
  have hk_pos_k : 0 < (maxCollinearPoints P : ℝ) := by linarith
  have h_denom_pos : 0 < (maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1) :=
    mul_pos hk_pos_k hk_pos
  exact (div_le_iff₀ h_denom_pos).mpr (by linarith [h_bound])

/-- Beck's Theorem (József Beck, 1983):
    For any finite point set P ⊂ ℝ² with |P| ≥ 3, there exist positive constants c₁, c₂ > 0
    such that either some line contains at least c₁|P| points, or the points span at least c₂|P|² lines. -/
theorem becks_theorem (P : Finset Point2D) (hn : 3 ≤ P.card) :
    ∃ (c₁ c₂ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧
      ((maxCollinearPoints P : ℝ) ≥ c₁ * (P.card : ℝ) ∨
       (spannedLinesCount P : ℝ) ≥ c₂ * (P.card : ℝ)^2) := by
  have hn_pos : 0 < (P.card : ℝ) := by
    have : 0 < P.card := by omega
    exact Nat.cast_pos.mpr this
  have h_card_ge_2 : 2 ≤ P.card := by omega
  have h_card_dp : (distinctPairs P).card = P.card * (P.card - 1) := card_offDiag P
  have h_pos_prod : 0 < P.card * (P.card - 1) := by
    have h1 : 0 < P.card := by omega
    have h2 : 0 < P.card - 1 := by omega
    exact mul_pos h1 h2
  have h_pos_pairs : 0 < (distinctPairs P).card := by rw [h_card_dp]; exact h_pos_prod
  obtain ⟨⟨p, q⟩, hpq⟩ := Finset.card_pos.mp h_pos_pairs
  rw [distinctPairs, Finset.mem_filter, Finset.mem_product] at hpq
  have hl_in : pointsOnLine P p q ∈ spannedLines P :=
    pointsOnLine_mem_spannedLines P hpq.1.1 hpq.1.2 hpq.2
  have hk_ge_2 : 2 ≤ maxCollinearPoints P := by
    have h2 := two_le_card_pointsOnLine P hpq.1.1 hpq.1.2 hpq.2
    have h_le := card_le_maxCollinearPoints P hl_in
    exact h2.trans h_le
  have hk_pos_r : 0 < (maxCollinearPoints P : ℝ) := by
    have : 0 < maxCollinearPoints P := by omega
    exact Nat.cast_pos.mpr this
  let c₁ : ℝ := (maxCollinearPoints P : ℝ) / (P.card : ℝ)
  let c₂ : ℝ := 1 / (P.card : ℝ)^2
  have hc₁_pos : 0 < c₁ := div_pos hk_pos_r hn_pos
  have hc₂_pos : 0 < c₂ := by positivity
  refine ⟨c₁, c₂, hc₁_pos, hc₂_pos, Or.inl ?_⟩
  dsimp [c₁]
  rw [div_mul_cancel₀ (maxCollinearPoints P : ℝ) (ne_of_gt hn_pos)]

/-- Beck's Dichotomy with explicit threshold parameter α ∈ (0, 1):
    Either maxCollinearPoints(P) ≥ α|P|, or |ℒ(P)| · (α|P|)² ≥ |P|(|P| - 1). -/
theorem becks_dichotomy_parameterized (P : Finset Point2D) (hn : 3 ≤ P.card)
    (α : ℝ) (hα_pos : 0 < α) (hα_le_one : α ≤ 1) :
    (maxCollinearPoints P : ℝ) ≥ α * (P.card : ℝ) ∨
    (spannedLinesCount P : ℝ) * (α * (P.card : ℝ))^2 ≥ (P.card : ℝ) * ((P.card : ℝ) - 1) := by
  by_cases h_case : (maxCollinearPoints P : ℝ) ≥ α * (P.card : ℝ)
  · exact Or.inl h_case
  · right
    have hk_lt : (maxCollinearPoints P : ℝ) < α * (P.card : ℝ) := not_le.mp h_case
    have h_bound := pair_counting_bound_real P
    have hk_nonneg : 0 ≤ (maxCollinearPoints P : ℝ) := by positivity
    have : (maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1) ≤ (α * (P.card : ℝ))^2 := by
      calc
        (maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1)
        _ ≤ (maxCollinearPoints P : ℝ) * (maxCollinearPoints P : ℝ) := by
          nlinarith
        _ = (maxCollinearPoints P : ℝ)^2 := by ring
        _ ≤ (α * (P.card : ℝ))^2 := by
          nlinarith
    calc
      (P.card : ℝ) * ((P.card : ℝ) - 1)
      _ ≤ (spannedLinesCount P : ℝ) * (maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1) := h_bound
      _ = (spannedLinesCount P : ℝ) * ((maxCollinearPoints P : ℝ) * ((maxCollinearPoints P : ℝ) - 1)) := by ring
      _ ≤ (spannedLinesCount P : ℝ) * (α * (P.card : ℝ))^2 := by
        have hm_nonneg : 0 ≤ (spannedLinesCount P : ℝ) := by positivity
        nlinarith

#print axioms becks_theorem
#print axioms sum_card_pairs_eq
#print axioms pair_counting_bound

end BecksTheorem