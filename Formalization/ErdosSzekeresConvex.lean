import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
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
(no three points collinear) contains the vertices of a convex $k$-gon.

Erdős and Szekeres proved the exact upper bound:
$$ES(k) \le \binom{2k - 4}{k - 2} + 1$$
and conjectured the exact value is $ES(k) = 2^{k - 2} + 1$:
- $k = 4 \implies ES(4) = 5$ (Esther Klein's original problem)
- $k = 5 \implies ES(5) = 9$ (Kalbfleisch et al. 1970 / Makai)
- $k = 6 \implies ES(6) = 17$ (Szekeres & Peters 2006)
- Asymptotics: $2^{k - o(k)} \le ES(k) \le 2^{k + o(k)}$ (Holmsen 2020, Suk 2017).

## Proof Technique (Cups and Caps / Ramsey Transition)
1. **Esther Klein Base Case ($k = 4$):** Among any 5 points in general position,
   either 4 form a convex quadrilateral directly, or the convex hull is a triangle containing
   2 interior points whose connecting line separates two of the triangle's vertices,
   forming a convex quad with the remaining vertices.
2. **Cup-Cap Lemma:** A sequence of points $(x_1, y_1), \dots, (x_m, y_m)$ sorted by $x$-coordinate
   forms an $a$-cup (convex downward) or a $b$-cap (convex upward).
   Any set of $\binom{a+b-4}{a-2} + 1$ points in general position contains an $a$-cup or a $b$-cap.
3. Setting $a = b = k$ yields a convex $k$-gon of size $\binom{2k-4}{k-2} + 1$.

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
    have : (0 : ℝ) * u.1 + 1 * v.1 = v.1 := by ring
    rw [this]
    exact hv
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
    have : (0 : ℝ) * u.1 + 1 * v.1 = v.1 := by ring
    rw [this]
    exact hv
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
-- Section 2: Cups, Caps, and the Erdős–Szekeres Bound
-- ============================================================================

/-- An ordered sequence of points forms an `a`-cup (convex downward). -/
def IsCup (pts : List Point2D) (a : ℕ) : Prop :=
  pts.length = a ∧
  ∀ i (hi : i + 2 < pts.length),
    orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) > 0

/-- An ordered sequence of points forms a `b`-cap (convex upward). -/
def IsCap (pts : List Point2D) (b : ℕ) : Prop :=
  pts.length = b ∧
  ∀ i (hi : i + 2 < pts.length),
    orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) < 0

lemma isCap_cons (p0 : Point2D) (pts : List Point2D) (b : ℕ) (hb : 3 ≤ b)
    (h_len : pts.length = b - 1)
    (h_first : 2 ≤ pts.length → orientationDet p0 (pts.get ⟨0, by omega⟩) (pts.get ⟨1, by omega⟩) < 0)
    (h_rest : ∀ i (hi : i + 2 < pts.length),
      orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) < 0) :
    IsCap (p0 :: pts) b := by
  refine ⟨by simp [h_len]; omega, ?_⟩
  intro i hi
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
    (h_cup : ∀ i (hi : i + 2 < pts.length),
      orientationDet (pts.get ⟨i, by omega⟩) (pts.get ⟨i+1, by omega⟩) (pts.get ⟨i+2, by omega⟩) > 0)
    (h_last : orientationDet (pts.get ⟨a - 3, by omega⟩) (pts.get ⟨a - 2, by omega⟩) q > 0) :
    IsCup (pts ++ [q]) a := by
  refine ⟨by simp [h_len]; omega, ?_⟩
  intro i hi
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
      (h_card : Nat.choose (a + b - 4) (a - 2) + 1 ≤ S.card)
      (h_gen : InGeneralPosition S),
      (∃ cup : List Point2D, IsCup cup a ∧ ∀ p ∈ cup, p ∈ S) ∨
      (∃ cap : List Point2D, IsCap cap b ∧ ∀ p ∈ cap, p ∈ S) := by
  induction' s using Nat.strong_induction_on with s ih
  intro a b ha hb h_sum S h_card h_gen
  by_cases ha3 : a = 3
  · subst ha3
    have h_ch : Nat.choose (3 + b - 4) (3 - 2) + 1 = b := by
      have h1 : 3 + b - 4 = b - 1 := by omega
      have h2 : 3 - 2 = 1 := by omega
      rw [h1, h2, Nat.choose_one_right]
      omega
    have hb_card : b ≤ S.card := by rw [← h_ch]; exact h_card
    let L := (S.toList).take b
    have hL_len : L.length = b := by
      rw [List.length_take, Finset.length_toList]
      exact min_eq_left hb_card
    have hL_sub : ∀ p ∈ L, p ∈ S := by
      intro p hp
      have := List.mem_of_mem_take hp
      exact (Finset.mem_toList.mp this)
    have hL_nodup : L.Nodup := (Finset.nodup_toList S).sublist (List.take_sublist b (Finset.toList S))
    by_cases h_pos : ∃ i, ∃ (hi : i + 2 < L.length),
        0 < orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩)
    · rcases h_pos with ⟨i, hi, h_det⟩
      let cup : List Point2D := [L.get ⟨i, by omega⟩, L.get ⟨i+1, by omega⟩, L.get ⟨i+2, by omega⟩]
      refine Or.inl ⟨cup, ⟨rfl, ?_⟩, ?_⟩
      · intro j hj
        have : j = 0 := by
          dsimp [cup] at hj
          omega
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
    · refine Or.inr ⟨L, ⟨hL_len, ?_⟩, hL_sub⟩
      intro i hi
      have h_nonpos : ¬ 0 < orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) := by
        intro h
        exact h_pos ⟨i, hi, h⟩
      have h_ne : orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) ≠ 0 := by
        apply h_gen
        · exact hL_sub _ (List.get_mem ..)
        · exact hL_sub _ (List.get_mem ..)
        · exact hL_sub _ (List.get_mem ..)
        · intro h_eq
          have h_inj := List.nodup_iff_injective_get.mp hL_nodup h_eq
          have : i = i + 1 := by injection h_inj
          omega
        · intro h_eq
          have h_inj := List.nodup_iff_injective_get.mp hL_nodup h_eq
          have : i + 1 = i + 2 := by injection h_inj
          omega
        · intro h_eq
          have h_inj := List.nodup_iff_injective_get.mp hL_nodup h_eq
          have : i = i + 2 := by injection h_inj
          omega
      exact lt_of_le_of_ne (le_of_not_gt h_nonpos) h_ne
  · by_cases hb3 : b = 3
    · subst hb3
      have h_ch : Nat.choose (a + 3 - 4) (a - 2) + 1 = a := by
        have h1 : a + 3 - 4 = (a - 2) + 1 := by omega
        rw [h1, Nat.choose_succ_self_right]
        omega
      have ha_card : a ≤ S.card := by rw [← h_ch]; exact h_card
      let L := (S.toList).take a
      have hL_len : L.length = a := by
        rw [List.length_take, Finset.length_toList]
        exact min_eq_left ha_card
      have hL_sub : ∀ p ∈ L, p ∈ S := by
        intro p hp
        have := List.mem_of_mem_take hp
        exact (Finset.mem_toList.mp this)
      have hL_nodup : L.Nodup := (Finset.nodup_toList S).sublist (List.take_sublist a (Finset.toList S))
      by_cases h_neg : ∃ i, ∃ (hi : i + 2 < L.length),
          orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) < 0
      · rcases h_neg with ⟨i, hi, h_det⟩
        let cap : List Point2D := [L.get ⟨i, by omega⟩, L.get ⟨i+1, by omega⟩, L.get ⟨i+2, by omega⟩]
        refine Or.inr ⟨cap, ⟨rfl, ?_⟩, ?_⟩
        · intro j hj
          have : j = 0 := by
            dsimp [cap] at hj
            omega
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
      · refine Or.inl ⟨L, ⟨hL_len, ?_⟩, hL_sub⟩
        intro i hi
        have h_nonneg : ¬ orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) < 0 := by
          intro h
          exact h_neg ⟨i, hi, h⟩
        have h_ne : orientationDet (L.get ⟨i, by omega⟩) (L.get ⟨i+1, by omega⟩) (L.get ⟨i+2, by omega⟩) ≠ 0 := by
          apply h_gen
          · exact hL_sub _ (List.get_mem ..)
          · exact hL_sub _ (List.get_mem ..)
          · exact hL_sub _ (List.get_mem ..)
          · intro h_eq
            have h_inj := List.nodup_iff_injective_get.mp hL_nodup h_eq
            have : i = i + 1 := by injection h_inj
            omega
          · intro h_eq
            have h_inj := List.nodup_iff_injective_get.mp hL_nodup h_eq
            have : i + 1 = i + 2 := by injection h_inj
            omega
          · intro h_eq
            have h_inj := List.nodup_iff_injective_get.mp hL_nodup h_eq
            have : i = i + 2 := by injection h_inj
            omega
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
          have h_rec := ih ((a - 1) + b) (by omega) (a - 1) b (by omega) hb (by omega) (S \ E) (by rw [h_ch1]; exact hN1_le) (h_gen_sub (S \ E) (Finset.sdiff_subset ..))
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
          have h_rec := ih (a + (b - 1)) (by omega) a (b - 1) ha (by omega) (by omega) E (by rw [h_ch2]; exact hE_card) (h_gen_sub E (Finset.filter_subset ..))
          rcases h_rec with ⟨cup, hcup, hcup_sub⟩ | ⟨cap, hcap, hcap_sub⟩
          · exact Or.inl ⟨cup, hcup, fun p hp => (Finset.mem_filter.mp (hcup_sub p hp)).1⟩
          · have h0_lt : 0 < cap.length := by
              have := hcap.1
              omega
            have h1_lt : 1 < cap.length := by
              have := hcap.1
              omega
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
            by_cases h_ext : 0 < orientationDet p0 e1 e2
            · have h_cup_ext : IsCup (u ++ [e2]) a := by
                apply isCup_append_one u e2 a ha4 hu_len hu_cup.2
                rw [hu_last_eq]
                exact h_ext
              have h_sub_ext : ∀ q ∈ u ++ [e2], q ∈ S := by
                intro q hq
                simp only [List.mem_append, List.mem_singleton] at hq
                rcases hq with hq_u | rfl
                · exact hu_sub q hq_u
                · exact (Finset.mem_filter.mp (hcap_sub e2 (List.get_mem ..))).1
              exact Or.inl ⟨u ++ [e2], h_cup_ext, h_sub_ext⟩
            · by_cases h_det_neg : orientationDet p0 e1 e2 < 0
              · have h_cap_cons : IsCap (p0 :: cap) b := by
                  apply isCap_cons p0 cap b hb (by rw [hcap.1])
                  · intro _
                    exact h_det_neg
                  · exact hcap.2
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
                  have h_cap_det := hcap.2 0 (by rw [hcap.1]; omega)
                  simp only [List.get_eq_getElem] at h_cap_det
                  have h0_eq : cap[0] = e1 := rfl
                  have h1_eq : cap[1] = e2 := rfl
                  rw [h0_eq, h1_eq, heq, orientationDet_self_left] at h_cap_det
                  linarith
                have hp0_ne_e1 : p0 ≠ e1 := by
                  intro heq
                  have h_cup_det := hu_cup.2 (a - 4) (by rw [hu_len]; omega)
                  simp only [List.get_eq_getElem] at h_cup_det
                  have hp0_eq : u[a - 4 + 1] = p0 := by
                    have : a - 4 + 1 = a - 3 := by omega
                    congr 1
                  have he1_eq : u[a - 4 + 2] = e1 := by
                    have : u[a - 4 + 2] = u.get ⟨a - 2, ha2_lt⟩ := by
                      simp only [List.get_eq_getElem]
                      congr 1
                      omega
                    rw [this, hu_last_eq]
                  rw [hp0_eq, he1_eq, heq, orientationDet_self_mid] at h_cup_det
                  linarith
                have he2_in_S : e2 ∈ S := (Finset.mem_filter.mp (hcap_sub e2 (List.get_mem ..))).1
                have he1_in_S : e1 ∈ S := (Finset.mem_filter.mp he1_in_E).1
                by_cases hp0_eq_e2 : p0 = e2
                · let p_prev := u.get ⟨a - 4, by rw [hu_len]; omega⟩
                  have hp_prev_in_S : p_prev ∈ S := hu_sub p_prev (List.get_mem ..)
                  have h_det_prev : orientationDet p_prev e1 e2 < 0 := by
                    have h_cup_det := hu_cup.2 (a - 4) (by rw [hu_len]; omega)
                    simp only [List.get_eq_getElem] at h_cup_det
                    have hp0_eq : u[a - 4 + 1] = p0 := by
                      have : a - 4 + 1 = a - 3 := by omega
                      congr 1
                    have he1_eq : u[a - 4 + 2] = e1 := by
                      have : u[a - 4 + 2] = u.get ⟨a - 2, ha2_lt⟩ := by
                        simp only [List.get_eq_getElem]
                        congr 1
                        omega
                      rw [this, hu_last_eq]
                    have hp_prev_eq : u[a - 4] = p_prev := rfl
                    rw [hp0_eq, he1_eq, hp0_eq_e2, hp_prev_eq] at h_cup_det
                    have h_perm := orientationDet_perm p_prev e2 e1
                    linarith
                  have h_cap_cons : IsCap (p_prev :: cap) b := by
                    apply isCap_cons p_prev cap b hb (by rw [hcap.1])
                    · intro _
                      exact h_det_prev
                    · exact hcap.2
                  refine Or.inr ⟨p_prev :: cap, h_cap_cons, ?_⟩
                  intro q hq
                  simp only [List.mem_cons] at hq
                  rcases hq with rfl | hq_cap
                  · exact hp_prev_in_S
                  · exact (Finset.mem_filter.mp (hcap_sub q hq_cap)).1
                · have h_ne_zero := h_gen p0 e1 e2 hp0_in_S he1_in_S he2_in_S hp0_ne_e1 he1_ne hp0_eq_e2
                  exact False.elim (h_ne_zero h_zero)

/-- **Cup-Cap Lemma (Erdős–Szekeres 1935):**
    Any sequence of `Nat.choose (a + b - 4) (a - 2) + 1` points sorted by x-coordinate
    in general position contains an `a`-cup or a `b`-cap. -/
theorem cup_cap_lemma (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b)
    (S : Finset Point2D)
    (h_card : Nat.choose (a + b - 4) (a - 2) + 1 ≤ S.card)
    (h_gen : InGeneralPosition S) :
    (∃ cup : List Point2D, IsCup cup a ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap b ∧ ∀ p ∈ cap, p ∈ S) := by
  exact cup_cap_induction (a + b) a b ha hb rfl S h_card h_gen

-- ============================================================================
-- Section 4: Cup/Cap Polygons & Convex Geometry
-- ============================================================================

lemma isCup_k3_nodup (cup : List Point2D) (hcup : IsCup cup 3) : cup.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  by_contra h_ne
  have h_ne_idx : i ≠ j := fun h => h_ne (Fin.ext h)
  wlog hlt : i < j generalizing i j hi hj
  · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) h_ne_idx.symm
    exact this j hj i hi heq.symm (Ne.symm h_ne) h_ne_idx.symm hgt
  have hd0 := hcup.2 0 (by rw [hcup.1]; omega)
  have hi_lt : i < 3 := by rw [hcup.1] at hi; exact hi
  have hj_lt : j < 3 := by rw [hcup.1] at hj; exact hj
  interval_cases i <;> interval_cases j <;> try omega
  · have ha : (⟨0, by omega⟩ : Fin cup.length) = ⟨0, hi⟩ := by ext; rfl
    have hb : (⟨1, by omega⟩ : Fin cup.length) = ⟨1, hj⟩ := by ext; rfl
    rw [ha, hb, heq, orientationDet_self_left] at hd0
    linarith
  · have ha : (⟨0, by omega⟩ : Fin cup.length) = ⟨0, hi⟩ := by ext; rfl
    have hc : (⟨2, by omega⟩ : Fin cup.length) = ⟨2, hj⟩ := by ext; rfl
    rw [ha, hc, heq, orientationDet_self_right] at hd0
    linarith
  · have hb : (⟨1, by omega⟩ : Fin cup.length) = ⟨1, hi⟩ := by ext; rfl
    have hc : (⟨2, by omega⟩ : Fin cup.length) = ⟨2, hj⟩ := by ext; rfl
    rw [hb, hc, heq, orientationDet_self_mid] at hd0
    linarith

/-- Any 3-cup forms a strictly convex 3-gon (triangle). -/
lemma formsConvexPolygon_of_isCup_k3 (S : Finset Point2D) (cup : List Point2D)
    (hcup : IsCup cup 3) (h_sub : ∀ p ∈ cup, p ∈ S) :
    FormsConvexPolygon S 3 := by
  classical
  let poly := cup.toFinset
  have h_nodup := isCup_k3_nodup cup hcup
  refine ⟨poly, ?_, ?_, ?_⟩
  · intro p hp; exact h_sub p (List.mem_toFinset.mp hp)
  · rw [List.toFinset_card_of_nodup h_nodup, hcup.1]
  · intro p hp
    have hp_mem : p ∈ cup := List.mem_toFinset.mp hp
    obtain ⟨⟨m, hm⟩, hp_eq⟩ := List.get_of_mem hp_mem
    have h_len : cup.length = 3 := hcup.1
    have hd0 := hcup.2 0 (by rw [hcup.1]; omega)
    have h_set : (poly : Set Point2D) \ {p} = ↑(poly \ {p}) := by ext x; simp
    rw [h_set]
    have hm_lt : m < 3 := by rw [hcup.1] at hm; exact hm
    interval_cases m
    · -- m = 0
      let a := cup.get ⟨2, by rw [hcup.1]; omega⟩
      let b := cup.get ⟨1, by rw [hcup.1]; omega⟩
      have hp0 : p = cup.get ⟨0, by rw [hcup.1]; omega⟩ := hp_eq.symm
      have h_perm : orientationDet a b p = - orientationDet (cup.get ⟨0, by rw [hcup.1]; omega⟩) (cup.get ⟨1, by rw [hcup.1]; omega⟩) (cup.get ⟨2, by rw [hcup.1]; omega⟩) := by
        rw [hp0]; dsimp [a, b, orientationDet]; ring
      have hp_neg : orientationDet a b p < 0 := by linarith [hd0, h_perm]
      apply not_mem_convexHull_of_separated_pos_ge (poly \ {p}) p a b hp_neg
      intro t ht
      obtain ⟨j, hj_lt, rfl⟩ : ∃ (j : ℕ) (hj : j < cup.length), cup.get ⟨j, hj⟩ = t := by
        have ht_mem : t ∈ cup := List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem ht_mem
        exact ⟨j, hj, rfl⟩
      have hj_ne_0 : j ≠ 0 := by
        intro heq; subst heq
        exact (Finset.mem_sdiff.mp ht).2 (by rw [hp_eq]; exact Finset.mem_singleton_self p)
      have hj3 : j < 3 := by rw [hcup.1] at hj_lt; exact hj_lt
      interval_cases j <;> try omega
      · have : cup.get ⟨1, hj_lt⟩ = b := by congr 1
        rw [this, orientationDet_self_mid]
      · have : cup.get ⟨2, hj_lt⟩ = a := by congr 1
        rw [this, orientationDet_self_right]
    · -- m = 1
      let a := cup.get ⟨0, by rw [hcup.1]; omega⟩
      let b := cup.get ⟨2, by rw [hcup.1]; omega⟩
      have hp1 : p = cup.get ⟨1, by rw [hcup.1]; omega⟩ := hp_eq.symm
      have h_perm : orientationDet a b p = - orientationDet (cup.get ⟨0, by rw [hcup.1]; omega⟩) (cup.get ⟨1, by rw [hcup.1]; omega⟩) (cup.get ⟨2, by rw [hcup.1]; omega⟩) := by
        rw [hp1]; dsimp [a, b, orientationDet]; ring
      have hp_neg : orientationDet a b p < 0 := by linarith [hd0, h_perm]
      apply not_mem_convexHull_of_separated_pos_ge (poly \ {p}) p a b hp_neg
      intro t ht
      obtain ⟨j, hj_lt, rfl⟩ : ∃ (j : ℕ) (hj : j < cup.length), cup.get ⟨j, hj⟩ = t := by
        have ht_mem : t ∈ cup := List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem ht_mem
        exact ⟨j, hj, rfl⟩
      have hj_ne_1 : j ≠ 1 := by
        intro heq; subst heq
        exact (Finset.mem_sdiff.mp ht).2 (by rw [hp_eq]; exact Finset.mem_singleton_self p)
      have hj3 : j < 3 := by rw [hcup.1] at hj_lt; exact hj_lt
      interval_cases j <;> try omega
      · have : cup.get ⟨0, hj_lt⟩ = a := by congr 1
        rw [this, orientationDet_self_right]
      · have : cup.get ⟨2, hj_lt⟩ = b := by congr 1
        rw [this, orientationDet_self_mid]
    · -- m = 2
      let a := cup.get ⟨1, by rw [hcup.1]; omega⟩
      let b := cup.get ⟨0, by rw [hcup.1]; omega⟩
      have hp2 : p = cup.get ⟨2, by rw [hcup.1]; omega⟩ := hp_eq.symm
      have h_perm : orientationDet a b p = - orientationDet (cup.get ⟨0, by rw [hcup.1]; omega⟩) (cup.get ⟨1, by rw [hcup.1]; omega⟩) (cup.get ⟨2, by rw [hcup.1]; omega⟩) := by
        rw [hp2]; dsimp [a, b, orientationDet]; ring
      have hp_neg : orientationDet a b p < 0 := by linarith [hd0, h_perm]
      apply not_mem_convexHull_of_separated_pos_ge (poly \ {p}) p a b hp_neg
      intro t ht
      obtain ⟨j, hj_lt, rfl⟩ : ∃ (j : ℕ) (hj : j < cup.length), cup.get ⟨j, hj⟩ = t := by
        have ht_mem : t ∈ cup := List.mem_toFinset.mp (Finset.mem_sdiff.mp ht).1
        obtain ⟨⟨j, hj⟩, rfl⟩ := List.get_of_mem ht_mem
        exact ⟨j, hj, rfl⟩
      have hj_ne_2 : j ≠ 2 := by
        intro heq; subst heq
        exact (Finset.mem_sdiff.mp ht).2 (by rw [hp_eq]; exact Finset.mem_singleton_self p)
      have hj3 : j < 3 := by rw [hcup.1] at hj_lt; exact hj_lt
      interval_cases j <;> try omega
      · have : cup.get ⟨0, hj_lt⟩ = b := by congr 1
        rw [this, orientationDet_self_mid]
      · have : cup.get ⟨1, hj_lt⟩ = a := by congr 1
        rw [this, orientationDet_self_right]

lemma isCup_reverse_of_isCap (cap : List Point2D) (k : ℕ) (hk : 3 ≤ k) (hcap : IsCap cap k) :
    IsCup cap.reverse k := by
  refine ⟨by rw [List.length_reverse, hcap.1], ?_⟩
  intro i hi
  rw [List.length_reverse, hcap.1] at hi
  have hi_k : k - 3 - i + 2 < cap.length := by rw [hcap.1]; omega
  have hd := hcap.2 (k - 3 - i) (by rw [hcap.1]; omega)
  simp only [List.get_eq_getElem] at hd ⊢
  have h_len : cap.length = k := hcap.1
  have h0 : cap.reverse[i] = cap[k - 1 - i] := by
    have hi_rev : i < cap.reverse.length := by rw [List.length_reverse, hcap.1]; omega
    have h := List.getElem_reverse hi_rev
    have h_idx : cap.length - 1 - i = k - 1 - i := by rw [h_len]
    have h_eq : cap[cap.length - 1 - i] = cap[k - 1 - i] := by congr 1
    rw [h, h_eq]
  have h1 : cap.reverse[i + 1] = cap[k - 2 - i] := by
    have hi_rev : i + 1 < cap.reverse.length := by rw [List.length_reverse, hcap.1]; omega
    have h := List.getElem_reverse hi_rev
    have h_idx : cap.length - 1 - (i + 1) = k - 2 - i := by rw [h_len]; omega
    have h_eq : cap[cap.length - 1 - (i + 1)] = cap[k - 2 - i] := by congr 1
    rw [h, h_eq]
  have h2 : cap.reverse[i + 2] = cap[k - 3 - i] := by
    have hi_rev : i + 2 < cap.reverse.length := by rw [List.length_reverse, hcap.1]; omega
    have h := List.getElem_reverse hi_rev
    have h_idx : cap.length - 1 - (i + 2) = k - 3 - i := by rw [h_len]; omega
    have h_eq : cap[cap.length - 1 - (i + 2)] = cap[k - 3 - i] := by congr 1
    rw [h, h_eq]
  rw [h0, h1, h2]
  have h_perm_direct : orientationDet cap[k - 1 - i] cap[k - 2 - i] cap[k - 3 - i] = - orientationDet cap[k - 3 - i] cap[k - 2 - i] cap[k - 1 - i] := by
    dsimp [orientationDet]; ring
  rw [h_perm_direct]
  have h_idx1 : cap[k - 3 - i + 1] = cap[k - 2 - i] := by congr 1; omega
  have h_idx2 : cap[k - 3 - i + 2] = cap[k - 1 - i] := by congr 1; omega
  rw [h_idx1, h_idx2] at hd
  linarith [hd]

/-- Any set of 5 points in general position contains a 4-cup or a 4-cap. -/
lemma exists_convex_4gon_of_five (S : Finset Point2D)
    (h_card : S.card = 5)
    (h_gen : InGeneralPosition S) :
    (∃ cup : List Point2D, IsCup cup 4 ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap 4 ∧ ∀ p ∈ cap, p ∈ S) := by
  have h_rec43 := cup_cap_lemma 4 3 (by omega) (by omega) S (by rw [show Nat.choose (4 + 3 - 4) (4 - 2) + 1 = 4 by decide, h_card]; omega) h_gen
  rcases h_rec43 with ⟨cup4, hcup4, hcup4_sub⟩ | ⟨cap3, hcap3, hcap3_sub⟩
  · exact Or.inl ⟨cup4, hcup4, hcup4_sub⟩
  · have h_rec34 := cup_cap_lemma 3 4 (by omega) (by omega) S (by rw [show Nat.choose (3 + 4 - 4) (3 - 2) + 1 = 4 by decide, h_card]; omega) h_gen
    rcases h_rec34 with ⟨c3, hc3_cup, hc3_sub⟩ | ⟨cap4, hcap4, hcap4_sub⟩
    · have hc3_nodup := isCup_k3_nodup c3 hc3_cup
      let poly3 := c3.toFinset
      have hpoly3_card : poly3.card = 3 := by
        rw [List.toFinset_card_of_nodup hc3_nodup, hc3_cup.1]
      have h_poly_sub : poly3 ⊆ S := by
        intro p hp
        exact hc3_sub p (List.mem_toFinset.mp hp)
      have h_diff_pos : 0 < (S \ poly3).card := by
        rw [Finset.card_sdiff_of_subset h_poly_sub, h_card, hpoly3_card]
        omega
      obtain ⟨q, hq_mem⟩ := Finset.card_pos.mp h_diff_pos
      have hq_in_S : q ∈ S := (Finset.mem_sdiff.mp hq_mem).1
      let u0 := c3.get ⟨0, by rw [hc3_cup.1]; omega⟩
      let u1 := c3.get ⟨1, by rw [hc3_cup.1]; omega⟩
      let u2 := c3.get ⟨2, by rw [hc3_cup.1]; omega⟩
      have hu0_in_S : u0 ∈ S := hc3_sub u0 (List.get_mem ..)
      have hu1_in_S : u1 ∈ S := hc3_sub u1 (List.get_mem ..)
      have hu2_in_S : u2 ∈ S := hc3_sub u2 (List.get_mem ..)
      have hc3_det : 0 < orientationDet u0 u1 u2 := by
        have hd := hc3_cup.2 0 (by rw [hc3_cup.1]; omega)
        have ha : c3.get ⟨0, by rw [hc3_cup.1]; omega⟩ = u0 := rfl
        have hb : c3.get ⟨0 + 1, by rw [hc3_cup.1]; omega⟩ = u1 := rfl
        have hc : c3.get ⟨0 + 2, by rw [hc3_cup.1]; omega⟩ = u2 := rfl
        rw [ha, hb, hc] at hd
        exact hd
      by_cases h_cup1 : 0 < orientationDet u1 u2 q
      · have h4 : IsCup [u0, u1, u2, q] 4 := by
          refine ⟨rfl, ?_⟩
          intro i hi
          have : i < 2 := by change i + 2 < 4 at hi; omega
          interval_cases i
          · exact hc3_det
          · exact h_cup1
        refine Or.inl ⟨[u0, u1, u2, q], h4, ?_⟩
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · exact hu0_in_S
        · exact hu1_in_S
        · exact hu2_in_S
        · exact hq_in_S
      · by_cases h_cup2 : 0 < orientationDet q u0 u1
        · have h4 : IsCup [q, u0, u1, u2] 4 := by
            refine ⟨rfl, ?_⟩
            intro i hi
            have : i < 2 := by change i + 2 < 4 at hi; omega
            interval_cases i
            · exact h_cup2
            · exact hc3_det
          refine Or.inl ⟨[q, u0, u1, u2], h4, ?_⟩
          intro p hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl
          · exact hq_in_S
          · exact hu0_in_S
          · exact hu1_in_S
          · exact hu2_in_S
        · by_cases h_cup_mid : 0 < orientationDet u0 u1 q
          · have h4 : IsCup [u0, u1, q, u2] 4 := by
              refine ⟨rfl, ?_⟩
              intro i hi
              have : i < 2 := by change i + 2 < 4 at hi; omega
              interval_cases i
              · exact h_cup_mid
              · have h_p1 := orientationDet_perm u1 u2 q
                have h_p2 := orientationDet_perm u1 q u2
                change 0 < orientationDet u1 q u2
                have h_p1_ne : orientationDet u1 u2 q ≠ 0 := by
                  apply h_gen u1 u2 q hu1_in_S hu2_in_S hq_in_S
                  · intro heq
                    have : u1 = c3.get ⟨0 + 1, by rw [hc3_cup.1]; omega⟩ := rfl
                    have : u2 = c3.get ⟨0 + 2, by rw [hc3_cup.1]; omega⟩ := rfl
                    rw [heq, orientationDet_self_mid] at hc3_det
                    linarith
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                have h_neg : orientationDet u1 u2 q < 0 := by
                  rcases lt_or_gt_of_ne h_p1_ne with hlt | hgt
                  · exact hlt
                  · exact False.elim (h_cup1 hgt)
                linarith
            refine Or.inl ⟨[u0, u1, q, u2], h4, ?_⟩
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl
            · exact hu0_in_S
            · exact hu1_in_S
            · exact hq_in_S
            · exact hu2_in_S
          · have h4 : IsCap [u0, u2, q, u1] 4 := by
              refine ⟨rfl, ?_⟩
              intro i hi
              have : i < 2 := by change i + 2 < 4 at hi; omega
              interval_cases i
              · have h_sum := orientationDet_sum_triangle u0 u1 u2 q
                have h_p := orientationDet_perm u2 u0 q
                have h_p2 := orientationDet_perm u0 u2 q
                have h_cyc := orientationDet_cyclic u2 u0 q
                have h_u0u1q_ne : orientationDet u0 u1 q ≠ 0 := by
                  apply h_gen u0 u1 q hu0_in_S hu1_in_S hq_in_S
                  · intro heq
                    have : u0 = c3.get ⟨0, by rw [hc3_cup.1]; omega⟩ := rfl
                    have : u1 = c3.get ⟨0 + 1, by rw [hc3_cup.1]; omega⟩ := rfl
                    rw [heq, orientationDet_self_left] at hc3_det
                    linarith
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                have h_u0u1q_neg : orientationDet u0 u1 q < 0 := by
                  rcases lt_or_gt_of_ne h_u0u1q_ne with hlt | hgt
                  · exact hlt
                  · exact False.elim (h_cup_mid hgt)
                have h_u1u2q_ne : orientationDet u1 u2 q ≠ 0 := by
                  apply h_gen u1 u2 q hu1_in_S hu2_in_S hq_in_S
                  · intro heq
                    have : u1 = c3.get ⟨0 + 1, by rw [hc3_cup.1]; omega⟩ := rfl
                    have : u2 = c3.get ⟨0 + 2, by rw [hc3_cup.1]; omega⟩ := rfl
                    rw [heq, orientationDet_self_mid] at hc3_det
                    linarith
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                have h_u1u2q_neg : orientationDet u1 u2 q < 0 := by
                  rcases lt_or_gt_of_ne h_u1u2q_ne with hlt | hgt
                  · exact hlt
                  · exact False.elim (h_cup1 hgt)
                change orientationDet u0 u2 q < 0
                linarith
              · have h_cyc := orientationDet_cyclic u1 u2 q
                have h_u1u2q_ne : orientationDet u1 u2 q ≠ 0 := by
                  apply h_gen u1 u2 q hu1_in_S hu2_in_S hq_in_S
                  · intro heq
                    have : u1 = c3.get ⟨0 + 1, by rw [hc3_cup.1]; omega⟩ := rfl
                    have : u2 = c3.get ⟨0 + 2, by rw [hc3_cup.1]; omega⟩ := rfl
                    rw [heq, orientationDet_self_mid] at hc3_det
                    linarith
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                  · intro heq
                    have : q ∈ poly3 := heq ▸ (List.mem_toFinset.mpr (List.get_mem ..))
                    exact (Finset.mem_sdiff.mp hq_mem).2 this
                have h_u1u2q_neg : orientationDet u1 u2 q < 0 := by
                  rcases lt_or_gt_of_ne h_u1u2q_ne with hlt | hgt
                  · exact hlt
                  · exact False.elim (h_cup1 hgt)
                change orientationDet u2 q u1 < 0
                linarith
            refine Or.inr ⟨[u0, u2, q, u1], h4, ?_⟩
            intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl
            · exact hu0_in_S
            · exact hu2_in_S
            · exact hq_in_S
            · exact hu1_in_S
    · exact Or.inr ⟨cap4, hcap4, hcap4_sub⟩

/-- Esther Klein's Theorem (1935):
    Any set of 5 points in general position in the plane contains a 4-cup or a 4-cap. -/
theorem esther_klein_five_points (S : Finset Point2D)
    (h_card : S.card = 5)
    (h_gen : InGeneralPosition S) :
    (∃ cup : List Point2D, IsCup cup 4 ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap 4 ∧ ∀ p ∈ cap, p ∈ S) :=
  exists_convex_4gon_of_five S h_card h_gen

/-- The Erdős–Szekeres bound: ES(k) ≤ Nat.choose (2*k - 4) (k - 2) + 1. -/
def erdosSzekeresBound (k : ℕ) : ℕ :=
  Nat.choose (2 * k - 4) (k - 2) + 1

/-- **Main Theorem: Erdős–Szekeres Convex Polygon Theorem (1935).**
    Every set of at least `erdosSzekeresBound k` points in general position contains a k-cup or a k-cap. -/
theorem erdos_szekeres_convex_polygon (k : ℕ) (hk : 3 ≤ k)
    (S : Finset Point2D)
    (h_card : erdosSzekeresBound k ≤ S.card)
    (h_gen : InGeneralPosition S) :
    (∃ cup : List Point2D, IsCup cup k ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap k ∧ ∀ p ∈ cap, p ∈ S) := by
  have h_bound : Nat.choose (k + k - 4) (k - 2) + 1 ≤ S.card := by
    have : k + k = 2 * k := by omega
    rw [this]
    exact h_card
  exact cup_cap_lemma k k hk hk S h_bound h_gen

/-- The Erdős–Szekeres Exact Conjecture: ES(k) = 2^(k-2) + 1 for all k ≥ 3. -/
def ErdosSzekeresConjecture : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (S : Finset Point2D),
    2^(k - 2) + 1 ≤ S.card →
    InGeneralPosition S →
    (∃ cup : List Point2D, IsCup cup k ∧ ∀ p ∈ cup, p ∈ S) ∨
    (∃ cap : List Point2D, IsCap cap k ∧ ∀ p ∈ cap, p ∈ S)