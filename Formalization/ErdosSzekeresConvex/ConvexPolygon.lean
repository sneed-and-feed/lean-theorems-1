import Formalization.ErdosSzekeresConvex.Orientation
import Formalization.ErdosSzekeresConvex.Sorting
import Formalization.ErdosSzekeresConvex.CupCap
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# Convex Polygon Formation from Cups and Caps

This module formalizes:
1. **4-Point Determinant Identities:** `orientationDet_four_p_r_s` and `orientationDet_four_p_q_s`.
2. **Transitivity of Orientations:**
   - `orientationDet_pos_prs_of_pqr_qrs`, `orientationDet_pos_pqs_of_pqr_qrs`
   - `orientationDet_neg_prs_of_pqr_qrs`, `orientationDet_neg_pqs_of_pqr_qrs`
3. **Global Orientation Bounds:**
   - `isCup_orientationDet_pos`: every triple in an $a$-cup has strictly positive determinant.
   - `isCap_orientationDet_neg`: every triple in a $b$-cap has strictly negative determinant.
4. **Convex Polygon Embedding:**
   - `formsConvexPolygon_of_isCup`: every $k$-cup ($k \ge 3$) forms the vertex set of a strictly convex $k$-gon.
   - `formsConvexPolygon_of_isCap`: every $k$-cap ($k \ge 3$) forms the vertex set of a strictly convex $k$-gon.
-/

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
