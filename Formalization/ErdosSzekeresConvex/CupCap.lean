import Formalization.ErdosSzekeresConvex.Orientation
import Formalization.ErdosSzekeresConvex.Sorting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic


open Finset

/-!
# Cups, Caps, and the Erdős–Szekeres Cup-Cap Theorem (1935)

This module formalizes:
1. **Cups & Caps:** `IsCup` (convex downward x-monotone sequence) and `IsCap` (convex upward x-monotone sequence).
2. **Monotonicity & Nodup Properties:** `isXMonotone_get_lt_step`, `isXMonotone_get_lt`, `isCup_nodup`, `isCap_nodup`.
3. **Extension Lemmas:** `isCap_cons` and `isCup_append_one`.
4. **Pascal Identity for Cup-Cap Bounds:** `choose_cup_cap_split`.
5. **Cup-Cap Lemma:** `cup_cap_induction` and `cup_cap_lemma` (every sequence of $\binom{a+b-4}{a-2}+1$ points
   in general position with distinct $x$-coordinates contains an $a$-cup or a $b$-cap).
-/

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
  · exact lt_trans (ih (by omega)) (hx _ h_ik)

lemma isXMonotone_get_lt (pts : List Point2D)
    (hx : ∀ i (hi : i + 1 < pts.length), (pts.get ⟨i, by omega⟩).1 < (pts.get ⟨i+1, by omega⟩).1)
    (i j : ℕ) (hi : i < pts.length) (hj : j < pts.length) (hij : i < j) :
    (pts.get ⟨i, hi⟩).1 < (pts.get ⟨j, hj⟩).1 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  exact isXMonotone_get_lt_step pts hx i k hj

lemma isCup_nodup (pts : List Point2D) (a : ℕ) (hcup : IsCup pts a) : pts.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim <| ne_of_lt (isXMonotone_get_lt pts hcup.2.1 i j hi hj h) (by rw [heq])
  · exact Fin.ext h
  · exact False.elim <| ne_of_gt (isXMonotone_get_lt pts hcup.2.1 j i hj hi h) (by rw [heq])

lemma isCap_nodup (pts : List Point2D) (b : ℕ) (hcap : IsCap pts b) : pts.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim <| ne_of_lt (isXMonotone_get_lt pts hcap.2.1 i j hi hj h) (by rw [heq])
  · exact Fin.ext h
  · exact False.elim <| ne_of_gt (isXMonotone_get_lt pts hcap.2.1 j i hj hi h) (by rw [heq])

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
    · exact h_x0 (by simp only [List.length_cons] at hi; omega)
    · exact h_x_rest i (by simp only [List.length_cons] at hi; omega)
  · intro i hi
    simp only [List.get_eq_getElem] at h_rest h_first ⊢
    rcases i with _ | i
    · exact h_first (by simp only [List.length_cons] at hi; omega)
    · exact h_rest i (by simp only [List.length_cons] at hi; omega)

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
    ∀ (a b : ℕ) (_ha : 3 ≤ a) (_hb : 3 ≤ b) (_h_sum : a + b = s)
      (S : Finset Point2D)
      (_h_dist : HasDistinctX S)
      (_h_card : Nat.choose (a + b - 4) (a - 2) + 1 ≤ S.card)
      (_h_gen : InGeneralPosition S),
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
    have hL_sub : ∀ p ∈ L, p ∈ S := fun p hp => by
      have := List.mem_toFinset.mpr (List.mem_of_mem_take hp)
      rwa [hL_toFinset] at this
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
      have hL_sub : ∀ p ∈ L, p ∈ S := fun p hp => by
        have := List.mem_toFinset.mpr (List.mem_of_mem_take hp)
        rwa [hL_toFinset] at this
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
      have : DecidablePred is_end := fun p => Classical.dec (is_end p)
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
