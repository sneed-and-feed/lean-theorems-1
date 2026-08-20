import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Polynomial

/-- Number of sign variations in a non-zero real sequence (ignoring zeros). -/
noncomputable def sign_variations : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | x :: y :: rest =>
    if x = 0 then sign_variations (y :: rest)
    else if y = 0 then sign_variations (x :: rest)
    else (if x * y < 0 then 1 else 0) + sign_variations (y :: rest)

/-- Sign variations of the non-zero coefficients of a polynomial p(X). -/
noncomputable def poly_sign_variations (p : Polynomial ℝ) : ℕ :=
  sign_variations (List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)))

/-- Total number of positive real roots of p(X) counted with algebraic multiplicity. -/
noncomputable def pos_roots_count (p : Polynomial ℝ) : ℕ :=
  (p.roots.filter (· > (0 : ℝ))).card

lemma sign_variations_cons_zero (l : List ℝ) :
    sign_variations (0 :: l) = sign_variations l := by
  cases l with
  | nil =>
    rw [sign_variations, sign_variations]
  | cons y rest =>
    rw [sign_variations]
    simp

lemma sign_variations_cons_nonzero_zero (x : ℝ) (rest : List ℝ) (hx : x ≠ 0) :
    sign_variations (x :: 0 :: rest) = sign_variations (x :: rest) := by
  rw [sign_variations]
  simp [hx]

lemma sign_variations_filter_ne_zero (l : List ℝ) :
    sign_variations l = sign_variations (l.filter (· ≠ 0)) := by
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    rcases l with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · rfl
    · by_cases hx : x = 0
      · subst hx
        simp [sign_variations]
      · simp [hx, sign_variations]
    · by_cases hx : x = 0
      · subst hx
        rw [sign_variations_cons_zero]
        have h_len : (y :: rest).length < n := by
          subst hn; simp
        have ih1 := ih (y :: rest).length h_len (y :: rest) rfl
        rw [ih1]
        have : (0 :: y :: rest).filter (· ≠ 0) = (y :: rest).filter (· ≠ 0) := by simp
        rw [this]
      · by_cases hy : y = 0
        · subst hy
          rw [sign_variations_cons_nonzero_zero _ _ hx]
          have h_len : (x :: rest).length < n := by
            subst hn; simp
          have ih1 := ih (x :: rest).length h_len (x :: rest) rfl
          rw [ih1]
          have : (x :: 0 :: rest).filter (· ≠ 0) = (x :: rest).filter (· ≠ 0) := by simp [hx]
          rw [this]
        · rw [sign_variations]
          simp only [hx, hy, ite_false]
          have h_len : (y :: rest).length < n := by
            subst hn; simp
          have ih1 := ih (y :: rest).length h_len (y :: rest) rfl
          have h_flt : (x :: y :: rest).filter (· ≠ 0) = x :: y :: (rest.filter (· ≠ 0)) := by
            simp [hx, hy]
          have h_flt2 : (y :: rest).filter (· ≠ 0) = y :: (rest.filter (· ≠ 0)) := by
            simp [hy]
          rw [h_flt, sign_variations]
          simp only [hx, hy, ite_false]
          rw [h_flt2] at ih1
          rw [ih1]

lemma sign_variations_nonzero_parity (l : List ℝ) (hl : ∀ x ∈ l, x ≠ 0) (hne : l ≠ []) :
    (Even (sign_variations l) ↔ 0 < l.head hne * l.getLast hne) := by
  generalize hn : l.length = n
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · contradiction
    · have ha : a ≠ 0 := hl a (by simp)
      have : sign_variations [a] = 0 := by rw [sign_variations]
      rw [this]
      have h_ev : Even 0 := ⟨0, rfl⟩
      simp only [List.head_cons, List.getLast_singleton, h_ev, true_iff]
      have : 0 < a * a := mul_self_pos.mpr ha
      exact this
    · have ha : a ≠ 0 := hl a (by simp)
      have hb : b ≠ 0 := hl b (by simp)
      have hrest_hl : ∀ x ∈ b :: rest, x ≠ 0 := fun x hx => hl x (List.mem_cons_of_mem a hx)
      have hne_b : b :: rest ≠ [] := by simp
      have h_len : (b :: rest).length < n := by subst hn; simp
      have ih_b := ih (b :: rest).length h_len (b :: rest) hrest_hl hne_b rfl
      have h_head : (a :: b :: rest).head hne = a := rfl
      have h_last : (a :: b :: rest).getLast hne = (b :: rest).getLast hne_b := rfl
      have h_head_b : (b :: rest).head hne_b = b := rfl
      rw [h_head, h_last]
      rw [sign_variations]
      simp only [ha, hb, ite_false]
      set t := (b :: rest).getLast hne_b
      rw [h_head_b] at ih_b
      have ht : t ≠ 0 := by
        apply hrest_hl
        exact List.getLast_mem hne_b
      have h_even_add_one (k : ℕ) : Even (1 + k) ↔ ¬ Even k := by
        rw [add_comm, Nat.even_add_one]
      by_cases hab : a * b < 0
      · simp only [hab, ite_true]
        rw [h_even_add_one, ih_b]
        have h_equiv : ¬ (0 < b * t) ↔ (0 < a * t) := by
          have h_prod : (a * b) * (b * t) = (a * t) * (b ^ 2) := by ring
          have hb2_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
          constructor
          · intro hnot
            have hbt_neg : b * t < 0 := by
              have : b * t ≠ 0 := mul_ne_zero hb ht
              rcases lt_trichotomy (b * t) 0 with h | h | h
              · exact h
              · contradiction
              · exfalso; exact hnot h
            have : 0 < (a * b) * (b * t) := mul_pos_of_neg_of_neg hab hbt_neg
            rw [h_prod] at this
            exact pos_of_mul_pos_left this (le_of_lt hb2_pos)
          · intro hat_pos hbt_pos
            have : 0 < (a * t) * (b ^ 2) := mul_pos hat_pos hb2_pos
            rw [← h_prod] at this
            have : (a * b) * (b * t) < 0 := mul_neg_of_neg_of_pos hab hbt_pos
            linarith
        exact h_equiv
      · simp only [hab, ite_false, zero_add, ih_b]
        have hab_pos : 0 < a * b := by
          have : a * b ≠ 0 := mul_ne_zero ha hb
          rcases lt_trichotomy (a * b) 0 with h | h | h
          · exfalso; exact hab h
          · contradiction
          · exact h
        have h_prod : (a * b) * (b * t) = (a * t) * (b ^ 2) := by ring
        have hb2_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
        constructor
        · intro hbt_pos
          have : 0 < (a * b) * (b * t) := mul_pos hab_pos hbt_pos
          rw [h_prod] at this
          exact pos_of_mul_pos_left this (le_of_lt hb2_pos)
        · intro hat_pos
          have : 0 < (a * t) * (b ^ 2) := mul_pos hat_pos hb2_pos
          rw [← h_prod] at this
          exact pos_of_mul_pos_right this (le_of_lt hab_pos)

lemma leadingCoeff_X_sub_C_mul (r : ℝ) (q : Polynomial ℝ) :
    leadingCoeff ((X - C r) * q) = leadingCoeff q := by
  have : Monic (X - C r) := monic_X_sub_C r
  exact leadingCoeff_monic_mul this

lemma trailingCoeff_X_sub_C (r : ℝ) (hr : 0 < r) :
    trailingCoeff (X - C r) = -r ∧ natTrailingDegree (X - C r) = 0 := by
  have h0 : coeff (X - C r) 0 = -r := by simp
  have h0_ne : coeff (X - C r) 0 ≠ 0 := by
    rw [h0]
    linarith
  have hdeg : natTrailingDegree (X - C r) = 0 := by
    rw [natTrailingDegree_eq_zero]
    exact Or.inr h0_ne
  have hcoeff : trailingCoeff (X - C r) = -r := by
    rw [trailingCoeff, hdeg, coeff_zero_eq_eval_zero]
    simp
  exact ⟨hcoeff, hdeg⟩

lemma trailingCoeff_X_sub_C_mul (r : ℝ) (hr : 0 < r) (q : Polynomial ℝ) (hq : q ≠ 0) :
    trailingCoeff ((X - C r) * q) = -r * trailingCoeff q ∧
    natTrailingDegree ((X - C r) * q) = natTrailingDegree q := by
  have hX : (X - C r) ≠ 0 := X_sub_C_ne_zero r
  have htr_X := trailingCoeff_X_sub_C r hr
  have hdeg : natTrailingDegree ((X - C r) * q) = natTrailingDegree q := by
    rw [natTrailingDegree_mul hX hq, htr_X.2, zero_add]
  have hcoeff : trailingCoeff ((X - C r) * q) = -r * trailingCoeff q := by
    have h_coeff_mul := coeff_mul_natTrailingDegree_add_natTrailingDegree (p := X - C r) (q := q)
    rw [htr_X.2, zero_add] at h_coeff_mul
    rw [trailingCoeff, hdeg]
    rw [h_coeff_mul, htr_X.1]
  exact ⟨hcoeff, hdeg⟩

lemma pos_roots_count_mul_X_sub_C (r : ℝ) (hr : 0 < r) {q : Polynomial ℝ} (hq : q ≠ 0) :
    pos_roots_count ((X - C r) * q) = pos_roots_count q + 1 := by
  have hX : (X - C r) ≠ 0 := X_sub_C_ne_zero r
  have hmul : (X - C r) * q ≠ 0 := mul_ne_zero hX hq
  rw [pos_roots_count, roots_mul hmul, roots_X_sub_C]
  have h_filt : Multiset.filter (· > (0 : ℝ)) ({r} + q.roots) =
      Multiset.filter (· > (0 : ℝ)) {r} + Multiset.filter (· > (0 : ℝ)) q.roots := by
    rw [Multiset.filter_add]
  have h_r : Multiset.filter (· > (0 : ℝ)) {r} = {r} := by
    rw [Multiset.filter_singleton]
    split_ifs with h
    · rfl
    · exfalso; exact h hr
  rw [h_filt, h_r, Multiset.card_add, Multiset.card_singleton, add_comm]
  rfl

lemma exists_pos_root_factor (p : Polynomial ℝ) (hp : p ≠ 0) (hpos : 0 < pos_roots_count p) :
    ∃ (r : ℝ) (_hr : 0 < r) (q : Polynomial ℝ), q ≠ 0 ∧ p = (X - C r) * q ∧ pos_roots_count p = pos_roots_count q + 1 := by
  have h_card : 0 < (p.roots.filter (· > (0 : ℝ))).card := hpos
  obtain ⟨r, hr_mem⟩ : ∃ r, r ∈ p.roots.filter (· > (0 : ℝ)) := by
    have h_ne : p.roots.filter (· > (0 : ℝ)) ≠ 0 := by
      intro h_emp
      rw [h_emp, Multiset.card_zero] at h_card
      linarith
    exact Multiset.exists_mem_of_ne_zero h_ne
  rw [Multiset.mem_filter] at hr_mem
  have hr : 0 < r := hr_mem.2
  have hr_root : IsRoot p r := isRoot_of_mem_roots hr_mem.1
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hr_root
  have hq : q ≠ 0 := right_ne_zero_of_mul hp
  refine ⟨r, hr, q, hq, rfl, ?_⟩
  exact pos_roots_count_mul_X_sub_C r hr hq

lemma sign_variations_append_singleton (l : List ℝ) (hl : ∀ y ∈ l, y ≠ 0) (hne : l ≠ []) (x : ℝ) (hx : x ≠ 0) :
    sign_variations (l ++ [x]) = sign_variations l + if l.getLast hne * x < 0 then 1 else 0 := by
  induction l with
  | nil => contradiction
  | cons a rest ih =>
    have ha : a ≠ 0 := hl a (by simp)
    cases rest with
    | nil =>
      have : [a] ++ [x] = [a, x] := rfl
      rw [this]
      have h1 : ¬ (a = 0) := ha
      have h2 : ¬ (x = 0) := hx
      have h_last : [a].getLast hne = a := rfl
      rw [h_last]
      have h_a_var : sign_variations [a] = 0 := by rw [sign_variations]
      have h_x_var : sign_variations [x] = 0 := by rw [sign_variations]
      rw [h_a_var]
      nth_rw 1 [sign_variations]
      simp only [h1, h2, ite_false, h_x_var, add_zero, zero_add]
    | cons b tail =>
      have hb : b ≠ 0 := hl b (by simp)
      have h_cons_append : (a :: b :: tail) ++ [x] = a :: b :: (tail ++ [x]) := rfl
      rw [h_cons_append]
      rw [sign_variations]
      have h1 : ¬ (a = 0) := ha
      have h2 : ¬ (b = 0) := hb
      simp only [h1, h2, ite_false]
      have hne_btail : b :: tail ≠ [] := by simp
      have h_last : (a :: b :: tail).getLast hne = (b :: tail).getLast hne_btail := rfl
      rw [h_last]
      have h_tail_hl : ∀ y ∈ b :: tail, y ≠ 0 := fun y hy => hl y (List.mem_cons_of_mem a hy)
      have ih_res := ih h_tail_hl hne_btail
      have h_btail_app : (b :: tail) ++ [x] = b :: (tail ++ [x]) := rfl
      rw [← h_btail_app]
      rw [ih_res]
      have h_var_l : sign_variations (a :: b :: tail) = (if a * b < 0 then 1 else 0) + sign_variations (b :: tail) := by
        rw [sign_variations]
        simp only [ha, hb, ite_false]
      rw [h_var_l]
      omega

lemma sign_variations_reverse (l : List ℝ) (hl : ∀ y ∈ l, y ≠ 0) :
    sign_variations l.reverse = sign_variations l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have ha : a ≠ 0 := hl a (by simp)
    cases rest with
    | nil => rfl
    | cons b tail =>
      have hb : b ≠ 0 := hl b (by simp)
      have h_rest_hl : ∀ y ∈ b :: tail, y ≠ 0 := fun y hy => hl y (List.mem_cons_of_mem a hy)
      have ih_rest := ih h_rest_hl
      have h_rev_cons : (a :: b :: tail).reverse = (b :: tail).reverse ++ [a] := by
        rw [List.reverse_cons]
      rw [h_rev_cons]
      have hne_rev : (b :: tail).reverse ≠ [] := by simp
      have h_rev_hl : ∀ y ∈ (b :: tail).reverse, y ≠ 0 := by
        intro y hy
        rw [List.mem_reverse] at hy
        exact h_rest_hl y hy
      rw [sign_variations_append_singleton (b :: tail).reverse h_rev_hl hne_rev a ha]
      rw [ih_rest]
      have h_last_rev : (b :: tail).reverse.getLast hne_rev = b := by
        rw [List.getLast_reverse]
        rfl
      rw [h_last_rev]
      have h_mul_comm : b * a = a * b := mul_comm b a
      rw [h_mul_comm]
      have h_var_cons : sign_variations (a :: b :: tail) = (if a * b < 0 then 1 else 0) + sign_variations (b :: tail) := by
        rw [sign_variations]
        simp only [ha, hb, ite_false]
      rw [h_var_cons]
      omega

lemma sign_variations_eq_destutter' (x : ℝ) (hx : x ≠ 0) (l : List ℝ) (hl : ∀ y ∈ l, y ≠ 0) :
    sign_variations (x :: l) = ((l.map SignType.sign).destutter' (· ≠ ·) (SignType.sign x)).length - 1 := by
  induction l generalizing x with
  | nil =>
    have : sign_variations [x] = 0 := by rw [sign_variations]
    rw [this, List.map_nil, List.destutter'_nil, List.length_singleton]
  | cons y rest ih =>
    have hy : y ≠ 0 := hl y (by simp)
    have hrest_hl : ∀ z ∈ rest, z ≠ 0 := fun z hz => hl z (List.mem_cons_of_mem y hz)
    have ih_y := ih y hy hrest_hl
    rw [sign_variations]
    have h1 : ¬ (x = 0) := hx
    have h2 : ¬ (y = 0) := hy
    simp only [h1, h2, ite_false]
    rw [List.map_cons, List.destutter'_cons]
    have h_sign_ne : (SignType.sign x ≠ SignType.sign y) ↔ (x * y < 0) := by
      rcases lt_trichotomy x 0 with hx_neg | hx_zero | hx_pos
      · rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
        · rw [sign_neg hx_neg, sign_neg hy_neg]
          simp [not_lt_of_gt (mul_pos_of_neg_of_neg hx_neg hy_neg)]
        · contradiction
        · rw [sign_neg hx_neg, sign_pos hy_pos]
          simp [mul_neg_of_neg_of_pos hx_neg hy_pos]
      · contradiction
      · rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
        · rw [sign_pos hx_pos, sign_neg hy_neg]
          simp [mul_neg_of_pos_of_neg hx_pos hy_neg]
        · contradiction
        · rw [sign_pos hx_pos, sign_pos hy_pos]
          simp [not_lt_of_gt (mul_pos hx_pos hy_pos)]
    by_cases hxy : x * y < 0
    · have h_ne : SignType.sign x ≠ SignType.sign y := h_sign_ne.mpr hxy
      rw [ite_eq_left h_ne, ite_eq_left hxy]
      rw [List.length_cons]
      rw [ih_y]
      have : 1 ≤ ((rest.map SignType.sign).destutter' (· ≠ ·) (SignType.sign y)).length :=
        List.length_pos_of_ne_nil (List.destutter'_ne_nil _ _)
      omega
    · have h_not_ne : ¬ (SignType.sign x ≠ SignType.sign y) := fun h => hxy (h_sign_ne.mp h)
      have h_eq : SignType.sign x = SignType.sign y := not_not.mp h_not_ne
      rw [ite_eq_right h_not_ne, ite_eq_right hxy, zero_add]
      rw [h_eq]
      exact ih_y

lemma range_map_eq_ofFn (n : ℕ) (f : ℕ → ℝ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f (i : ℕ)) := by
  symm
  rw [← List.ofFn_getElem_eq_map (List.range n) f]
  simp

lemma filter_map_sign_eq (l : List ℝ) :
    (l.filter (· ≠ 0)).map SignType.sign = (l.map SignType.sign).filter (· ≠ 0) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    by_cases hx : x = 0
    · subst hx
      have h_flt : ((0 : ℝ) :: rest).filter (· ≠ 0) = rest.filter (· ≠ 0) := by
        simp
      have h_map_flt : (((0 : ℝ) :: rest).map SignType.sign).filter (· ≠ 0) =
          (rest.map SignType.sign).filter (· ≠ 0) := by
        simp
      rw [h_flt, h_map_flt, ih]
    · have hsx : SignType.sign x ≠ 0 := by
        intro h
        rw [sign_eq_zero_iff] at h
        exact hx h
      have h_flt : (x :: rest).filter (· ≠ 0) = x :: rest.filter (· ≠ 0) := by
        simp [hx]
      have h_map_flt : ((x :: rest).map SignType.sign).filter (· ≠ 0) =
          SignType.sign x :: (rest.map SignType.sign).filter (· ≠ 0) := by
        simp [hsx]
      rw [h_flt, List.map_cons, h_map_flt, ih]

lemma poly_sign_variations_eq_signVariations (p : Polynomial ℝ) :
    poly_sign_variations p = Polynomial.signVariations p := by
  by_cases hp : p = 0
  · subst hp
    have h1 : poly_sign_variations 0 = 0 := by
      rw [poly_sign_variations, natDegree_zero]
      have : List.ofFn (fun i : Fin 1 => (0 : Polynomial ℝ).coeff (i : ℕ)) = [0] := by
        simp [List.ofFn_succ]
      rw [this, sign_variations]
    rw [h1, signVariations_zero]
  · have h_coeffList : coeffList p = (List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ))).reverse := by
      rw [coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
      have h_ofFn : List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ)) =
          (List.range (p.natDegree + 1)).map p.coeff := by
        rw [range_map_eq_ofFn]
      rw [h_ofFn, List.map_reverse]
    rw [poly_sign_variations, signVariations]
    set L := List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ))
    rw [sign_variations_filter_ne_zero L]
    have h_hl : ∀ x ∈ L.filter (· ≠ 0), x ≠ 0 := by
      intro x hx
      simp only [List.mem_filter, decide_eq_true_eq] at hx
      exact hx.2
    rw [← sign_variations_reverse (L.filter (· ≠ 0)) h_hl]
    rw [← List.filter_reverse]
    have h_L_rev : L.reverse = coeffList p := h_coeffList.symm
    rw [h_L_rev]
    have h_lead_ne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have h_lead_mem : p.leadingCoeff ∈ (coeffList p).filter (· ≠ 0) := by
      rw [List.mem_filter]
      refine ⟨?_, by simp [h_lead_ne]⟩
      rw [h_coeffList, List.mem_reverse, List.mem_ofFn]
      exact ⟨⟨p.natDegree, Nat.lt_succ_self _⟩, rfl⟩
    have h_ne_nil : (coeffList p).filter (· ≠ 0) ≠ [] := by
      intro h_emp
      rw [h_emp] at h_lead_mem
      contradiction
    obtain ⟨s, ss, h_cl⟩ := List.exists_cons_of_ne_nil h_ne_nil
    have hs : s ≠ 0 := by
      have : s ∈ (coeffList p).filter (· ≠ 0) := by rw [h_cl]; simp
      simp only [List.mem_filter, decide_eq_true_eq] at this
      exact this.2
    have hss : ∀ y ∈ ss, y ≠ 0 := by
      intro y hy
      have : y ∈ (coeffList p).filter (· ≠ 0) := by rw [h_cl]; simp [hy]
      simp only [List.mem_filter, decide_eq_true_eq] at this
      exact this.2
    have h_s_ss : ((coeffList p).map SignType.sign).filter (· ≠ 0) =
        SignType.sign s :: (ss.map SignType.sign) := by
      rw [← filter_map_sign_eq, h_cl, List.map_cons]
    rw [h_cl]
    rw [sign_variations_eq_destutter' s hs ss hss]
    rw [h_s_ss, List.destutter_cons']

/-- Sub-lemma 1: Base case for linear factor roots. -/
lemma root_factor_pos_sign_variation (r : ℝ) (hr : 0 < r) :
    pos_roots_count (X - C r) = 1 ∧ poly_sign_variations (X - C r) = 1 := by
  constructor
  · rw [pos_roots_count, roots_X_sub_C]
    have hf : Multiset.filter (· > (0 : ℝ)) {r} = {r} := by
      rw [Multiset.filter_singleton]
      split_ifs with h
      · rfl
      · exfalso; exact h hr
    rw [hf, Multiset.card_singleton]
  · rw [poly_sign_variations]
    have hdeg : (X - C r).natDegree = 1 := natDegree_X_sub_C r
    rw [hdeg]
    have h_list : List.ofFn (fun i : Fin 2 => (X - C r).coeff (i : ℕ)) = [-r, 1] := by
      have : List.ofFn (fun i : Fin 2 => (X - C r).coeff (i : ℕ)) =
          [(X - C r).coeff 0, (X - C r).coeff 1] := by
        simp [List.ofFn_succ]
      rw [this]
      simp
    rw [h_list]
    rw [sign_variations]
    have h1 : ¬ (-r = 0) := by linarith
    have h2 : ¬ (1 : ℝ) = 0 := by norm_num
    have h3 : -r * 1 < 0 := by linarith
    simp only [h1, h2, h3, ite_true, ite_false, sign_variations]

lemma pos_roots_count_le_poly_sign_variations (p : Polynomial ℝ) :
    pos_roots_count p ≤ poly_sign_variations p := by
  rw [poly_sign_variations_eq_signVariations, pos_roots_count]
  have h_countP : (p.roots.filter (· > (0 : ℝ))).card = p.roots.countP (0 < ·) := by
    rw [Multiset.countP_eq_card_filter]
  rw [h_countP]
  exact roots_countP_pos_le_signVariations p

lemma trailingCoeff_eraseLead (p : Polynomial ℝ) (he : p.eraseLead ≠ 0) :
    trailingCoeff p = trailingCoeff p.eraseLead ∧ natTrailingDegree p = natTrailingDegree p.eraseLead := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp at he
  have htr_mem := natTrailingDegree_mem_support_of_nonzero he
  have htr_lt : p.eraseLead.natTrailingDegree < p.natDegree :=
    lt_natDegree_of_mem_eraseLead_support htr_mem
  have h_coeff_eq (n : ℕ) (hn : n ≠ p.natDegree) : p.coeff n = p.eraseLead.coeff n :=
    (eraseLead_coeff_of_ne n hn).symm
  have h_tr_deg : natTrailingDegree p = natTrailingDegree p.eraseLead := by
    apply le_antisymm
    · apply natTrailingDegree_le_of_ne_zero
      rw [h_coeff_eq _ (ne_of_lt htr_lt)]
      exact coeff_natTrailingDegree_ne_zero.mpr he
    · apply le_natTrailingDegree hp
      intro m hm
      have hm_ne : m ≠ p.natDegree := ne_of_lt (lt_trans hm htr_lt)
      rw [h_coeff_eq m hm_ne]
      exact coeff_eq_zero_of_lt_natTrailingDegree hm
  have h_tr_coeff : trailingCoeff p = trailingCoeff p.eraseLead := by
    rw [trailingCoeff, trailingCoeff, h_tr_deg, h_coeff_eq _ (ne_of_lt htr_lt)]
  exact ⟨h_tr_coeff, h_tr_deg⟩

lemma coeffList_filter_ne_zero_head_getLast (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ (hne : (coeffList p).filter (· ≠ 0) ≠ []),
      ((coeffList p).filter (· ≠ 0)).head hne = leadingCoeff p ∧
      ((coeffList p).filter (· ≠ 0)).getLast hne = trailingCoeff p := by
  generalize hd : p.natDegree = d
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
    have h_lead_ne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have h_cl := coeffList_eraseLead hp
    have h_filt_rep (k : ℕ) : (List.replicate k (0 : ℝ)).filter (· ≠ 0) = [] := by
      induction k with
      | zero => rfl
      | succ k _ihk => simp [List.replicate_succ]
    by_cases he : p.eraseLead = 0
    · have h_cl_mon : coeffList p = p.leadingCoeff :: List.replicate (p.natDegree - p.eraseLead.degree.succ) 0 := by
        rw [h_cl, he, coeffList_zero, List.append_nil]
      have h_flt : (coeffList p).filter (· ≠ 0) = [p.leadingCoeff] := by
        rw [h_cl_mon, List.filter_cons, ite_eq_left (by simp [h_lead_ne]), h_filt_rep]
      have hne : (coeffList p).filter (· ≠ 0) ≠ [] := by rw [h_flt]; simp
      have h_head : ((coeffList p).filter (· ≠ 0)).head hne = p.leadingCoeff := by
        have : ((coeffList p).filter (· ≠ 0)).head hne = [p.leadingCoeff].head (by simp) := by congr 1
        rw [this]; rfl
      have h_last : ((coeffList p).filter (· ≠ 0)).getLast hne = p.leadingCoeff := by
        have : ((coeffList p).filter (· ≠ 0)).getLast hne = [p.leadingCoeff].getLast (by simp) := by congr 1
        rw [this]; rfl
      have h_tr : p.trailingCoeff = p.leadingCoeff := by
        have h_mon : p = monomial p.natDegree p.leadingCoeff := by
          have := eraseLead_add_monomial_natDegree_leadingCoeff p
          rw [he, zero_add] at this
          exact this.symm
        nth_rw 1 [h_mon]
        rw [trailingCoeff, natTrailingDegree_monomial h_lead_ne, coeff_monomial_same]
      refine ⟨hne, h_head, by rw [h_last, ← h_tr]⟩
    · have h_deg_lt : p.eraseLead.natDegree < d := by
        subst hd
        have hpos := natDegree_pos_of_eraseLead_ne_zero he
        exact eraseLead_natDegree_le p |>.trans_lt (Nat.sub_lt hpos Nat.one_pos)
      obtain ⟨hne_e, h_head_e, h_last_e⟩ := ih p.eraseLead.natDegree h_deg_lt p.eraseLead he rfl
      have h_flt : (coeffList p).filter (· ≠ 0) = p.leadingCoeff :: (coeffList p.eraseLead).filter (· ≠ 0) := by
        rw [h_cl, List.filter_cons, ite_eq_left (by simp [h_lead_ne]), List.filter_append, h_filt_rep, List.nil_append]
      have hne : (coeffList p).filter (· ≠ 0) ≠ [] := by rw [h_flt]; simp
      have h_head : ((coeffList p).filter (· ≠ 0)).head hne = p.leadingCoeff := by
        have : ((coeffList p).filter (· ≠ 0)).head hne = (p.leadingCoeff :: (coeffList p.eraseLead).filter (· ≠ 0)).head (by simp) := by congr 1
        rw [this]; rfl
      have h_last : ((coeffList p).filter (· ≠ 0)).getLast hne = ((coeffList p.eraseLead).filter (· ≠ 0)).getLast hne_e := by
        have : ((coeffList p).filter (· ≠ 0)).getLast hne = (p.leadingCoeff :: (coeffList p.eraseLead).filter (· ≠ 0)).getLast (by simp) := by congr 1
        rw [this, List.getLast_cons hne_e]
      have h_tr := trailingCoeff_eraseLead p he
      rw [h_tr.1]
      refine ⟨hne, h_head, by rw [h_last, h_last_e]⟩

lemma poly_sign_variations_parity (p : Polynomial ℝ) (hp : p ≠ 0) :
    (Even (poly_sign_variations p) ↔ 0 < trailingCoeff p * leadingCoeff p) := by
  rw [poly_sign_variations]
  set L := List.ofFn (fun i : Fin (p.natDegree + 1) => p.coeff (i : ℕ))
  rw [sign_variations_filter_ne_zero L]
  have h_coeffList : coeffList p = L.reverse := by
    rw [coeffList, withBotSucc_degree_eq_natDegree_add_one hp]
    rw [List.map_reverse, range_map_eq_ofFn]
  have h_flt_rev : L.filter (· ≠ 0) = ((coeffList p).filter (· ≠ 0)).reverse := by
    rw [h_coeffList, List.filter_reverse, List.reverse_reverse]
  obtain ⟨hne_cl, h_head_cl, h_last_cl⟩ := coeffList_filter_ne_zero_head_getLast p hp
  have hne_L : L.filter (· ≠ 0) ≠ [] := by
    rw [h_flt_rev]
    exact mt List.reverse_eq_nil_iff.mp hne_cl
  have hl_nonzero : ∀ x ∈ L.filter (· ≠ 0), x ≠ 0 := by
    intro x hx
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2
  have h_parity := sign_variations_nonzero_parity (L.filter (· ≠ 0)) hl_nonzero hne_L
  rw [h_parity]
  have hne_rev_cl : ((coeffList p).filter (· ≠ 0)).reverse ≠ [] := by
    exact mt List.reverse_eq_nil_iff.mp hne_cl
  have h_head_L : (L.filter (· ≠ 0)).head hne_L = trailingCoeff p := by
    have : (L.filter (· ≠ 0)).head hne_L = (((coeffList p).filter (· ≠ 0)).reverse).head hne_rev_cl := by
      congr 1
    rw [this, List.head_reverse, h_last_cl]
  have h_last_L : (L.filter (· ≠ 0)).getLast hne_L = leadingCoeff p := by
    have : (L.filter (· ≠ 0)).getLast hne_L = (((coeffList p).filter (· ≠ 0)).reverse).getLast hne_rev_cl := by
      congr 1
    rw [this, List.getLast_reverse, h_head_cl]
  rw [h_head_L, h_last_L]

lemma trailingCoeff_mul_leadingCoeff_pos_of_pos_roots_count_zero (p : Polynomial ℝ) (hp : p ≠ 0) (hpos : pos_roots_count p = 0) :
    0 < trailingCoeff p * leadingCoeff p := by
  generalize hd : p.natDegree = d
  induction d using Nat.strong_induction_on generalizing p with
  | h d ih =>
    by_cases hc0 : p.coeff 0 ≠ 0
    · have htr_deg : p.natTrailingDegree = 0 := by
        rw [natTrailingDegree_eq_zero]
        exact Or.inr hc0
      have htr_coeff : trailingCoeff p = p.eval 0 := by
        rw [trailingCoeff, htr_deg, coeff_zero_eq_eval_zero]
      have hroots : ∀ y, p.IsRoot y → y < 0 := by
        intro y hy
        have hy_mem : y ∈ p.roots := mem_roots hp |>.mpr hy
        by_contra hy_not
        have hy_ge : 0 ≤ y := not_lt.mp hy_not
        rcases eq_or_lt_of_le hy_ge with rfl | hy_pos
        · have : p.eval 0 = 0 := hy
          rw [coeff_zero_eq_eval_zero] at hc0
          exact hc0 this
        · have hy_filt : y ∈ p.roots.filter (· > (0 : ℝ)) := by
            rw [Multiset.mem_filter]
            exact ⟨hy_mem, hy_pos⟩
          have : 0 < (p.roots.filter (· > (0 : ℝ))).card :=
            Multiset.card_pos_iff_exists_mem.mpr ⟨y, hy_filt⟩
          rw [← pos_roots_count] at this
          omega
      have hlead_ne : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
      rcases lt_trichotomy p.leadingCoeff 0 with hneg | hz | hpos_lead
      · have heval_neg := eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hroots (le_of_lt hneg)
        rw [← htr_coeff] at heval_neg
        exact mul_pos_of_neg_of_neg heval_neg hneg
      · contradiction
      · have heval_pos := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroots (le_of_lt hpos_lead)
        rw [← htr_coeff] at heval_pos
        exact mul_pos heval_pos hpos_lead
    · have hc0_eq : p.coeff 0 = 0 := not_not.mp hc0
      have h_eval0 : p.eval 0 = 0 := by rw [← coeff_zero_eq_eval_zero, hc0_eq]
      have h_root0 : p.IsRoot 0 := h_eval0
      obtain ⟨q, hq_eq⟩ := dvd_iff_isRoot.mpr h_root0
      have hp_X_mul : p = X * q := by
        rw [hq_eq, map_zero, sub_zero]
      have hq : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hp_X_mul
        exact hp hp_X_mul
      have h_deg : p.natDegree = q.natDegree + 1 := by
        rw [hp_X_mul, natDegree_mul X_ne_zero hq, natDegree_X, add_comm]
      have h_deg_lt : q.natDegree < d := by
        subst hd; omega
      have h_pos_q : pos_roots_count q = 0 := by
        rw [pos_roots_count] at hpos ⊢
        have h_roots : p.roots = {0} + q.roots := by
          rw [hp_X_mul, roots_mul (mul_ne_zero X_ne_zero hq), roots_X]
        rw [h_roots, Multiset.filter_add] at hpos
        have h_filt0 : Multiset.filter (· > (0 : ℝ)) {0} = 0 := by
          rw [Multiset.filter_singleton]
          split_ifs with h
          · exfalso; linarith
          · rfl
        rw [h_filt0, zero_add] at hpos
        exact hpos
      have ih_q := ih q.natDegree h_deg_lt q hq h_pos_q rfl
      have h_lead : p.leadingCoeff = q.leadingCoeff := by
        rw [hp_X_mul, leadingCoeff_mul, leadingCoeff_X, one_mul]
      have h_tr : p.trailingCoeff = q.trailingCoeff := by
        have htr_mul := coeff_mul_natTrailingDegree_add_natTrailingDegree (p := (X : Polynomial ℝ)) (q := q)
        have h_tr_X : natTrailingDegree (X : Polynomial ℝ) = 1 := natTrailingDegree_X
        have h_coeff_X : trailingCoeff (X : Polynomial ℝ) = 1 := by
          rw [trailingCoeff, h_tr_X, coeff_X_one]
        rw [h_tr_X, h_coeff_X, one_mul] at htr_mul
        have h_tr_p : natTrailingDegree p = 1 + natTrailingDegree q := by
          rw [hp_X_mul, natTrailingDegree_mul X_ne_zero hq, h_tr_X, add_comm]
        rw [trailingCoeff, h_tr_p, hp_X_mul, htr_mul]
      rw [h_lead, h_tr]
      exact ih_q

/-- Main Theorem: Descartes's Rule of Signs (1637, Freek Wiedijk 100 Theorems #73).
    The number of positive roots of a real polynomial p(X) ≠ 0 (with multiplicity)
    is bounded above by the number of sign variations in its coefficients,
    and differs from it by an even integer. -/
theorem descartes_rule_of_signs (p : Polynomial ℝ) (hp : p ≠ 0) :
    pos_roots_count p ≤ poly_sign_variations p ∧
    Even (poly_sign_variations p - pos_roots_count p) := by
  refine ⟨pos_roots_count_le_poly_sign_variations p, ?_⟩
  generalize hk : pos_roots_count p = k
  induction k using Nat.strong_induction_on generalizing p with
  | h k ih =>
    subst hk
    by_cases hk0 : pos_roots_count p = 0
    · rw [hk0, tsub_zero]
      have hpos_prod := trailingCoeff_mul_leadingCoeff_pos_of_pos_roots_count_zero p hp hk0
      exact (poly_sign_variations_parity p hp).mpr hpos_prod
    · have h_pos_gt : 0 < pos_roots_count p := Nat.pos_of_ne_zero hk0
      obtain ⟨r, hr, q, hq, hp_eq, h_pos_count⟩ := exists_pos_root_factor p hp h_pos_gt
      have h_k_lt : pos_roots_count q < pos_roots_count p := by
        rw [h_pos_count]; omega
      have ih_q := ih (pos_roots_count q) h_k_lt q hq rfl
      have h_lead : leadingCoeff p = leadingCoeff q := by
        rw [hp_eq, leadingCoeff_X_sub_C_mul]
      have h_tr := trailingCoeff_X_sub_C_mul r hr q hq
      have h_tr_p : trailingCoeff p = -r * trailingCoeff q := by
        rw [hp_eq, h_tr.1]
      have h_prod : trailingCoeff p * leadingCoeff p = -r * (trailingCoeff q * leadingCoeff q) := by
        rw [h_tr_p, h_lead, mul_assoc]
      have h_parity_flip : (0 < trailingCoeff p * leadingCoeff p) ↔ ¬ (0 < trailingCoeff q * leadingCoeff q) := by
        rw [h_prod]
        constructor
        · intro h_pos h_q_pos
          have : 0 < -r * (trailingCoeff q * leadingCoeff q) := h_pos
          have h_neg : -r * (trailingCoeff q * leadingCoeff q) < 0 :=
            mul_neg_of_neg_of_pos (neg_lt_zero.mpr hr) h_q_pos
          linarith
        · intro h_not_pos
          have h_q_neg : trailingCoeff q * leadingCoeff q < 0 := by
            rcases lt_trichotomy (trailingCoeff q * leadingCoeff q) 0 with h | h | h
            · exact h
            · have hq_lead_ne := leadingCoeff_ne_zero.mpr hq
              have hq_tr_ne := trailingCoeff_nonzero_iff_nonzero.mpr hq
              have : trailingCoeff q * leadingCoeff q ≠ 0 := mul_ne_zero hq_tr_ne hq_lead_ne
              contradiction
            · exfalso; exact h_not_pos h
          exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hr) h_q_neg
      have h_var_flip : Even (poly_sign_variations p) ↔ ¬ Even (poly_sign_variations q) := by
        rw [poly_sign_variations_parity p hp, poly_sign_variations_parity q hq]
        exact h_parity_flip
      have h_le_p := pos_roots_count_le_poly_sign_variations p
      have h_le_q := pos_roots_count_le_poly_sign_variations q
      have h_sub_even_p : Even (poly_sign_variations p - pos_roots_count p) ↔
          (Even (poly_sign_variations p) ↔ Even (pos_roots_count p)) :=
        Nat.even_sub h_le_p
      have h_sub_even_q : Even (poly_sign_variations q - pos_roots_count q) ↔
          (Even (poly_sign_variations q) ↔ Even (pos_roots_count q)) :=
        Nat.even_sub h_le_q
      rw [h_sub_even_p]
      rw [h_sub_even_q] at ih_q
      rw [h_pos_count, Nat.even_add_one]
      rw [h_var_flip]
      tauto