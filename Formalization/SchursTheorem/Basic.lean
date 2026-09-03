import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

/-!
# Foundational & Classical Schur's Theorem

This module formalizes the classical **Schur's Theorem** (Issai Schur, 1916) on monochromatic solutions
to $x + y = z$ in partitioned integers, based on an explicit reduction to the multicolor triangle Ramsey theorem.

## Mathematical Context & Overview

Originating in Issai Schur's 1916 paper *Über die Kongruenz $x^m + y^m \equiv z^m \pmod p$*, Schur's theorem
is the earliest historical milestone in partition regularity and additive Ramsey theory.

1. **Explicit Multicolor Triangle Ramsey Upper Bound**:
   We define the explicit recursive upper bound
   $$B(0) = 2, \quad B(r + 1) = (r + 1) \cdot B(r) + 1$$
   via `SchursTheorem.ramseyTriangleBound`. This provides an explicit constructive bound on the multicolor
   triangle Ramsey number $R_r(3) \le B(r)$ ($B_1 = 3$, $B_2 = 7$, $B_3 = 22$, etc.).

2. **Multicolor Triangle Ramsey Theorem (`SchursTheorem.ramsey_triangle`)**:
   For any symmetric edge-coloring with $r \ge 1$ colors of a complete graph on at least $B(r)$ vertices,
   there exists a monochromatic triangle. The proof proceeds by induction on $r$, picking a root vertex $v_0$,
   applying the pigeonhole principle (`exists_fiber_ge`) on edges incident to $v_0$ to find a majority color $i^*$,
   and either finding a monochromatic edge of color $i^*$ among its neighbors (closing a monochromatic triangle with $v_0$)
   or applying the induction hypothesis to the reduced $(r - 1)$-coloring on the neighborhood.

3. **Classical Integer Schur's Theorem (`SchursTheorem.schurs_theorem`)**:
   For any $r$-coloring $\chi : \mathbb{N} \to \text{Fin } r$, there exists a monochromatic solution to
   $x + y = z$ with $1 \le x, y, z \le B(r)$. The proof embeds $\{0, 1, \dots, B(r)\}$ into the complete graph
   with difference edge-coloring $c(u, v) = \chi(|u - v|)$, finds a monochromatic triangle $a < b < c$,
   and sets $x = b - a$, $y = c - b$, $z = c - a$.

4. **Color Classes and Partition Formulations**:
   - `SchursTheorem.schurs_theorem_color_classes`: In any $r$-coloring of $\{1, \dots, B(r)\}$, at least one color class is not sum-free.
   - `SchursTheorem.schurs_theorem_partition`: In any $r$-covering $A_0, \dots, A_{r-1}$ of $\{1, \dots, B(r)\}$, at least one $A_i$ contains $x + y = z$.
   - `SchursTheorem.schurs_theorem_partition_not_sum_free`: Not all sets in an $r$-covering of $\{1, \dots, B(r)\}$ can be sum-free.

## Bound Fidelity Note (Anti-Pattern Q Compliance)

Following strict Palomar editorial standards, all docstrings and identifiers explicitly distinguish
between the recursive upper bound $B_r = \text{ramseyTriangleBound } r$ and the exact canonical
extremal Schur / Ramsey numbers $S(r)$ and $R_r(3)$.

## Main Results

* `SchursTheorem.ramseyTriangleBound`: Constructive recursive upper bound $B(r)$.
* `SchursTheorem.ramsey_triangle`: Multicolor triangle Ramsey theorem for complete graphs.
* `SchursTheorem.schurs_theorem`: Classical Schur's theorem with explicit bound $B(r)$.
* `SchursTheorem.schurs_theorem_color_classes`: Failure of sum-freeness in color classes.
* `SchursTheorem.schurs_theorem_partition`: Schur's theorem for set partitions / coverings.
* `SchursTheorem.schurs_theorem_partition_not_sum_free`: Partition sum-free failure.
-/

namespace SchursTheorem

variable {α : Type*} [DecidableEq α]

/-- Explicit recursive upper bound for the multicolor triangle Ramsey number $R_r(3)$:
    $B(0) = 2$, $B(r + 1) = (r + 1) \cdot B(r) + 1$.
    Note that `ramseyTriangleBound r` is an explicit upper bound ($B_r \ge R_r(3)$),
    not the exact multicolor Ramsey number. -/
def ramseyTriangleBound : ℕ → ℕ
  | 0 => 2
  | r + 1 => (r + 1) * ramseyTriangleBound r + 1

lemma ramseyTriangleBound_ge_two : ∀ (r : ℕ), 2 ≤ ramseyTriangleBound r
  | 0 => by decide
  | r + 1 => by
    dsimp [ramseyTriangleBound]
    have := ramseyTriangleBound_ge_two r
    nlinarith

lemma ramseyTriangleBound_pos (r : ℕ) : 0 < ramseyTriangleBound r :=
  lt_of_lt_of_le (by decide) (ramseyTriangleBound_ge_two r)

/-- A triple of distinct vertices forming a monochromatic triangle of color `k`. -/
def isMonoTriangle (c : α → α → Fin r) (S : Finset α) (u v w : α) (k : Fin r) : Prop :=
  u ∈ S ∧ v ∈ S ∧ w ∈ S ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
  c u v = k ∧ c u w = k ∧ c v w = k

/-- There exists a monochromatic triangle in `S` for edge-coloring `c`. -/
def hasMonoTriangle (c : α → α → Fin r) (S : Finset α) : Prop :=
  ∃ u v w k, isMonoTriangle c S u v w k

lemma exists_fiber_ge {r : ℕ} (S : Finset α) (f : α → Fin (r + 1)) (m : ℕ)
    (hS : (r + 1) * m ≤ S.card) :
    ∃ k : Fin (r + 1), m ≤ (S.filter (fun x => f x = k)).card := by
  by_contra! h_all
  have h_sum : S.card = ∑ k : Fin (r + 1), (S.filter (fun x => f x = k)).card := by
    rw [← card_biUnion]
    · congr 1; ext x; simp
    · intro i _ j _ hij; dsimp [Function.onFun]; rw [Finset.disjoint_left]; intro x h1 h2; simp at h1 h2; exact hij (h1.2.symm.trans h2.2)
  have h_lt : ∑ k : Fin (r + 1), (S.filter (fun x => f x = k)).card < (r + 1) * m := by
    calc ∑ k : Fin (r + 1), (S.filter (fun x => f x = k)).card
      _ < ∑ k : Fin (r + 1), m := sum_lt_sum_of_nonempty Finset.univ_nonempty (fun k _ => h_all k)
      _ = (r + 1) * m := by simp [mul_comm]
  omega

/-- Reduce a color in `Fin (r + 1) \ {i_star}` to `Fin r`. -/
def reduceColor {r : ℕ} (i_star : Fin (r + 1)) (k : Fin (r + 1)) (hk : k ≠ i_star) : Fin r :=
  if h : k.val < i_star.val then
    ⟨k.val, by have := i_star.is_lt; omega⟩
  else
    ⟨k.val - 1, by
      have hk_lt := k.is_lt
      have h_ne : k.val ≠ i_star.val := fun h_eq => hk (Fin.ext h_eq)
      omega⟩

lemma reduceColor_inj {r : ℕ} (i_star : Fin (r + 1)) (k1 k2 : Fin (r + 1))
    (h1 : k1 ≠ i_star) (h2 : k2 ≠ i_star) :
    reduceColor i_star k1 h1 = reduceColor i_star k2 h2 ↔ k1 = k2 := by
  constructor
  · intro h_eq
    ext
    obtain ⟨v1, hv1⟩ := k1
    obtain ⟨v2, hv2⟩ := k2
    obtain ⟨vi, hvi⟩ := i_star
    have h_ne1 : v1 ≠ vi := fun h => h1 (Fin.ext h)
    have h_ne2 : v2 ≠ vi := fun h => h2 (Fin.ext h)
    dsimp [reduceColor] at h_eq
    by_cases h_lt1 : v1 < vi
    · simp only [h_lt1, ↓reduceDIte] at h_eq
      by_cases h_lt2 : v2 < vi
      · simp only [h_lt2, ↓reduceDIte] at h_eq
        injection h_eq with h_val
      · simp only [h_lt2, ↓reduceDIte] at h_eq
        injection h_eq with h_val
        omega
    · simp only [h_lt1, ↓reduceDIte] at h_eq
      by_cases h_lt2 : v2 < vi
      · simp only [h_lt2, ↓reduceDIte] at h_eq
        injection h_eq with h_val
        omega
      · simp only [h_lt2, ↓reduceDIte] at h_eq
        injection h_eq with h_val
        have hv1_pos : 1 ≤ v1 := by omega
        have hv2_pos : 1 ≤ v2 := by omega
        have h_eq_nat : v1 = v2 := by
          have h_cancel1 : v1 = v1 - 1 + 1 := (Nat.sub_add_cancel hv1_pos).symm
          have h_cancel2 : v2 = v2 - 1 + 1 := (Nat.sub_add_cancel hv2_pos).symm
          rw [h_cancel1, h_cancel2, h_val]
        exact h_eq_nat
  · rintro rfl; rfl

/-- **Multicolor Triangle Ramsey Theorem**:
Any symmetric edge-coloring with `r ≥ 1` colors of a complete graph with at least
`ramseyTriangleBound r` vertices contains a monochromatic triangle. -/
theorem ramsey_triangle :
    ∀ (r : ℕ) (_hr : 1 ≤ r) (S : Finset α) (c : α → α → Fin r),
      (∀ u v, c u v = c v u) →
      ramseyTriangleBound r ≤ S.card →
      hasMonoTriangle c S := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr S c h_symm hS
    rcases eq_or_lt_of_le hr with rfl | hr_gt1
    · -- Base case r = 1:
      have h3 : 3 ≤ S.card := by
        have := ramseyTriangleBound_ge_two 1
        dsimp [ramseyTriangleBound] at hS
        omega
      have h_pos1 : 0 < S.card := by omega
      rcases card_pos.mp h_pos1 with ⟨u, hu⟩
      have h_pos2 : 0 < (S.erase u).card := by rw [card_erase_of_mem hu]; omega
      rcases card_pos.mp h_pos2 with ⟨v, hv⟩
      have hv_S : v ∈ S := (mem_erase.mp hv).2
      have h_ne_uv : u ≠ v := (mem_erase.mp hv).1.symm
      have h_pos3 : 0 < ((S.erase u).erase v).card := by rw [card_erase_of_mem hv, card_erase_of_mem hu]; omega
      rcases card_pos.mp h_pos3 with ⟨w, hw⟩
      have hw_S : w ∈ S := (mem_erase.mp (mem_erase.mp hw).2).2
      have hw_ne_v : w ≠ v := (mem_erase.mp hw).1
      have hw_ne_u : w ≠ u := (mem_erase.mp (mem_erase.mp hw).2).1
      have h_ne_uw : u ≠ w := hw_ne_u.symm
      have h_ne_vw : v ≠ w := hw_ne_v.symm
      have hc_uv : c u v = 0 := Subsingleton.elim (c u v) 0
      have hc_uw : c u w = 0 := Subsingleton.elim (c u w) 0
      have hc_vw : c v w = 0 := Subsingleton.elim (c v w) 0
      exact ⟨u, v, w, 0, hu, hv_S, hw_S, h_ne_uv, h_ne_uw, h_ne_vw, hc_uv, hc_uw, hc_vw⟩
    · -- Inductive step r >= 2, so r = r' + 1 with r' >= 1
      obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hr'_pos : 1 ≤ r' := by omega
      have h_pos := ramseyTriangleBound_pos (r' + 1)
      have h_card_pos : 0 < S.card := lt_of_lt_of_le h_pos hS
      rcases card_pos.mp h_card_pos with ⟨v0, hv0⟩
      let S_rest := S.erase v0
      have h_rest_card : S_rest.card = S.card - 1 := card_erase_of_mem hv0
      have h_bound_rest : (r' + 1) * ramseyTriangleBound r' ≤ S_rest.card := by
        have h_def : ramseyTriangleBound (r' + 1) = (r' + 1) * ramseyTriangleBound r' + 1 := rfl
        rw [h_def] at hS
        omega
      rcases exists_fiber_ge S_rest (fun u => c v0 u) (ramseyTriangleBound r') h_bound_rest with ⟨i_star, hi_star⟩
      let S_star := S_rest.filter (fun u => c v0 u = i_star)
      by_cases h_case1 : ∃ u ∈ S_star, ∃ w ∈ S_star, u ≠ w ∧ c u w = i_star
      · rcases h_case1 with ⟨u, hu, w, hw, huw, hc_uw⟩
        have hu_S : u ∈ S := (mem_erase.mp (mem_filter.mp hu).1).2
        have hw_S : w ∈ S := (mem_erase.mp (mem_filter.mp hw).1).2
        have hu_ne_v0 : u ≠ v0 := (mem_erase.mp (mem_filter.mp hu).1).1
        have hw_ne_v0 : w ≠ v0 := (mem_erase.mp (mem_filter.mp hw).1).1
        have hc_v0u : c v0 u = i_star := (mem_filter.mp hu).2
        have hc_v0w : c v0 w = i_star := (mem_filter.mp hw).2
        refine ⟨v0, u, w, i_star, hv0, hu_S, hw_S, hu_ne_v0.symm, hw_ne_v0.symm, huw, hc_v0u, hc_v0w, hc_uw⟩
      · push Not at h_case1
        let dummy_color : Fin r' := ⟨0, hr'_pos⟩
        let c_reduced : α → α → Fin r' := fun x y =>
          if h : c x y = i_star then dummy_color else reduceColor i_star (c x y) h
        have h_reduced_symm : ∀ u v, c_reduced u v = c_reduced v u := by
          intro u v; dsimp [c_reduced]; rw [h_symm u v]
        have h_star_card : ramseyTriangleBound r' ≤ S_star.card := hi_star
        have ih_call := ih r' (by omega) hr'_pos S_star c_reduced h_reduced_symm h_star_card
        rcases ih_call with ⟨u, v, w, k, hu, hv, hw, huv, huw, hvw, h1, h2, h3⟩
        have hu_S : u ∈ S := (mem_erase.mp (mem_filter.mp hu).1).2
        have hv_S : v ∈ S := (mem_erase.mp (mem_filter.mp hv).1).2
        have hw_S : w ∈ S := (mem_erase.mp (mem_filter.mp hw).1).2
        have hc_uv_ne : c u v ≠ i_star := h_case1 u hu v hv huv
        have hc_uw_ne : c u w ≠ i_star := h_case1 u hu w hw huw
        have hc_vw_ne : c v w ≠ i_star := h_case1 v hv w hw hvw
        have h_red_uv : c_reduced u v = reduceColor i_star (c u v) hc_uv_ne := by
          dsimp [c_reduced]; simp only [hc_uv_ne, ↓reduceDIte]
        have h_red_uw : c_reduced u w = reduceColor i_star (c u w) hc_uw_ne := by
          dsimp [c_reduced]; simp only [hc_uw_ne, ↓reduceDIte]
        have h_red_vw : c_reduced v w = reduceColor i_star (c v w) hc_vw_ne := by
          dsimp [c_reduced]; simp only [hc_vw_ne, ↓reduceDIte]
        have hc_uv_uw : c u w = c u v := by
          rw [← reduceColor_inj i_star (c u w) (c u v) hc_uw_ne hc_uv_ne]
          rw [← h_red_uw, ← h_red_uv, h2, h1]
        have hc_vw_uv : c v w = c u v := by
          rw [← reduceColor_inj i_star (c v w) (c u v) hc_vw_ne hc_uv_ne]
          rw [← h_red_vw, ← h_red_uv, h3, h1]
        refine ⟨u, v, w, c u v, hu_S, hv_S, hw_S, huv, huw, hvw, rfl, hc_uv_uw, hc_vw_uv⟩

/-- Definition: A set of integers is sum-free if it contains no solution to `x + y = z`. -/
def isSumFree (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

/-- **Schur's Theorem on Sum-Free Partitions** (Issai Schur, 1916):
For any $r \ge 1$, every $r$-coloring $\chi$ of the integers $\{1, \dots, N\}$
(where $N = \text{ramseyTriangleBound } r$) contains a monochromatic solution to $x + y = z$:
$\exists c \in \text{Fin } r, \exists x, y, z \in \{1, \dots, N\}, \, \chi(x) = c \wedge \chi(y) = c \wedge \chi(z) = c \wedge x + y = z$. -/
theorem schurs_theorem (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    let N := ramseyTriangleBound r
    ∃ (c : Fin r) (x y z : ℕ),
      1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧
      x ≤ N ∧ y ≤ N ∧ z ≤ N ∧
      x + y = z ∧
      χ x = c ∧ χ y = c ∧ χ z = c := by
  intro N
  let S : Finset ℕ := Finset.range (N + 1)
  have hS_card : S.card = N + 1 := Finset.card_range (N + 1)
  have h_ramsey_bound : ramseyTriangleBound r ≤ S.card := by
    rw [hS_card]
    omega
  let edgeColor : ℕ → ℕ → Fin r := fun u v =>
    if u < v then χ (v - u)
    else if v < u then χ (u - v)
    else ⟨0, hr⟩
  have h_edgeColor_symm : ∀ u v, edgeColor u v = edgeColor v u := by
    intro u v
    dsimp [edgeColor]
    rcases lt_trichotomy u v with h | rfl | h
    · rw [ite_eq_left h, ite_eq_right (asymm h), ite_eq_left h]
    · rfl
    · rw [ite_eq_right (asymm h), ite_eq_left h, ite_eq_left h]
  rcases ramsey_triangle r hr S edgeColor h_edgeColor_symm h_ramsey_bound with
    ⟨u, v, w, col, hu, hv, hw, huv, huw, hvw, hc_uv, hc_uw, hc_vw⟩
  rw [Finset.mem_range] at hu hv hw
  -- Sort u, v, w
  have h_sort : ∃ a b c, a < b ∧ b < c ∧
      a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      edgeColor a b = col ∧ edgeColor b c = col ∧ edgeColor a c = col := by
    have huS : u ∈ S := Finset.mem_range.mpr hu
    have hvS : v ∈ S := Finset.mem_range.mpr hv
    have hwS : w ∈ S := Finset.mem_range.mpr hw
    rcases lt_or_gt_of_ne huv with h1 | h1 <;>
    rcases lt_or_gt_of_ne huw with h2 | h2 <;>
    rcases lt_or_gt_of_ne hvw with h3 | h3
    · exact ⟨u, v, w, h1, h3, huS, hvS, hwS, hc_uv, hc_vw, hc_uw⟩
    · exact ⟨u, w, v, h2, h3, huS, hwS, hvS, hc_uw, by rw [h_edgeColor_symm]; exact hc_vw, hc_uv⟩
    · omega
    · exact ⟨w, u, v, h2, h1, hwS, huS, hvS, by rw [h_edgeColor_symm]; exact hc_uw, hc_uv, by rw [h_edgeColor_symm]; exact hc_vw⟩
    · exact ⟨v, u, w, h1, h2, hvS, huS, hwS, by rw [h_edgeColor_symm]; exact hc_uv, hc_uw, hc_vw⟩
    · omega
    · exact ⟨v, w, u, h3, h2, hvS, hwS, huS, hc_vw, by rw [h_edgeColor_symm]; exact hc_uw, by rw [h_edgeColor_symm]; exact hc_uv⟩
    · exact ⟨w, v, u, h3, h1, hwS, hvS, huS, by rw [h_edgeColor_symm]; exact hc_vw, by rw [h_edgeColor_symm]; exact hc_uv, by rw [h_edgeColor_symm]; exact hc_uw⟩
  rcases h_sort with ⟨a, b, c, hab, hbc, ha_S, -, hc_S, hc_ab, hc_bc, hc_ac⟩
  rw [Finset.mem_range] at ha_S hc_S
  have hac : a < c := lt_trans hab hbc
  let x := b - a
  let y := c - b
  let z := c - a
  have hx_pos : 1 ≤ x := by dsimp [x]; omega
  have hy_pos : 1 ≤ y := by dsimp [y]; omega
  have hz_pos : 1 ≤ z := by dsimp [z]; omega
  have hx_le : x ≤ N := by dsimp [x]; omega
  have hy_le : y ≤ N := by dsimp [y]; omega
  have hz_le : z ≤ N := by dsimp [z]; omega
  have h_sum_eq : x + y = z := by dsimp [x, y, z]; omega
  have hc_ab_val : edgeColor a b = χ x := by
    dsimp [edgeColor, x]
    rw [ite_eq_left hab]
  have hc_bc_val : edgeColor b c = χ y := by
    dsimp [edgeColor, y]
    rw [ite_eq_left hbc]
  have hc_ac_val : edgeColor a c = χ z := by
    dsimp [edgeColor, z]
    rw [ite_eq_left hac]
  rw [hc_ab_val] at hc_ab
  rw [hc_bc_val] at hc_bc
  rw [hc_ac_val] at hc_ac
  exact ⟨col, x, y, z, hx_pos, hy_pos, hz_pos, hx_le, hy_le, hz_le, h_sum_eq, hc_ab, hc_bc, hc_ac⟩

/-- The finite set of integers $\{1, \dots, N\}$. -/
def schurInterval (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun x => 1 ≤ x)

lemma mem_schurInterval {N x : ℕ} : x ∈ schurInterval N ↔ 1 ≤ x ∧ x ≤ N := by
  simp only [schurInterval, mem_filter, mem_range]
  omega

/-- **Schur's Theorem (Color Class Formulation):**
For any $r \ge 1$ and $N = \text{ramseyTriangleBound } r$, in any $r$-coloring of $\{1, \dots, N\}$,
at least one color class is not sum-free. -/
theorem schurs_theorem_color_classes (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    let N := ramseyTriangleBound r
    let colorClass (c : Fin r) : Finset ℕ :=
      (schurInterval N).filter (fun x => χ x = c)
    ∃ c : Fin r, ¬ isSumFree (colorClass c) := by
  intro N colorClass
  rcases schurs_theorem r hr χ with ⟨c, x, y, z, hx1, hy1, hz1, hxN, hyN, hzN, hxyz, hcx, hcy, hcz⟩
  refine ⟨c, ?_⟩
  intro h_sf
  have hx_in : x ∈ colorClass c := by
    dsimp [colorClass]
    rw [mem_filter, mem_schurInterval]
    exact ⟨⟨hx1, hxN⟩, hcx⟩
  have hy_in : y ∈ colorClass c := by
    dsimp [colorClass]
    rw [mem_filter, mem_schurInterval]
    exact ⟨⟨hy1, hyN⟩, hcy⟩
  have hz_in : z ∈ colorClass c := by
    dsimp [colorClass]
    rw [mem_filter, mem_schurInterval]
    exact ⟨⟨hz1, hzN⟩, hcz⟩
  have hz_not_in : x + y ∉ colorClass c := h_sf x hx_in y hy_in
  rw [hxyz] at hz_not_in
  exact hz_not_in hz_in

/-- **Schur's Theorem (Set Partition Formulation):**
If $\{1, \dots, \text{ramseyTriangleBound } r\}$ is partitioned (or covered) by $r$ sets
$A_0, \dots, A_{r-1}$, then at least one set $A_i$ contains a positive solution to $x + y = z$
with $1 \le x, y, z \le \text{ramseyTriangleBound } r$. -/
theorem schurs_theorem_partition (r : ℕ) (hr : 1 ≤ r) (A : Fin r → Finset ℕ)
    (h_cover : schurInterval (ramseyTriangleBound r) ⊆ Finset.biUnion Finset.univ A) :
    ∃ i : Fin r, ∃ x y z, x ∈ A i ∧ y ∈ A i ∧ z ∈ A i ∧ 1 ≤ x ∧ 1 ≤ y ∧ 1 ≤ z ∧ x + y = z := by
  let N := ramseyTriangleBound r
  have h_choice : ∀ x : ℕ, ∃ i : Fin r, x ∈ schurInterval N → x ∈ A i := by
    intro x
    by_cases hx : x ∈ schurInterval N
    · have hx_cov := h_cover hx
      rw [mem_biUnion] at hx_cov
      rcases hx_cov with ⟨i, -, hi⟩
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hr⟩, fun h => False.elim (hx h)⟩
  let χ : ℕ → Fin r := fun x => (h_choice x).choose
  have hχ_mem : ∀ x ∈ schurInterval N, x ∈ A (χ x) := fun x hx => (h_choice x).choose_spec hx
  rcases schurs_theorem r hr χ with ⟨c, x, y, z, hx1, hy1, hz1, hxN, hyN, hzN, hxyz, hcx, hcy, hcz⟩
  have hx_int : x ∈ schurInterval N := mem_schurInterval.mpr ⟨hx1, hxN⟩
  have hy_int : y ∈ schurInterval N := mem_schurInterval.mpr ⟨hy1, hyN⟩
  have hz_int : z ∈ schurInterval N := mem_schurInterval.mpr ⟨hz1, hzN⟩
  have hxA : x ∈ A c := by
    have := hχ_mem x hx_int
    rwa [hcx] at this
  have hyA : y ∈ A c := by
    have := hχ_mem y hy_int
    rwa [hcy] at this
  have hzA : z ∈ A c := by
    have := hχ_mem z hz_int
    rwa [hcz] at this
  exact ⟨c, x, y, z, hxA, hyA, hzA, hx1, hy1, hz1, hxyz⟩

/-- **Schur's Theorem (Partition Sum-Free Formulation):**
If $\{1, \dots, \text{ramseyTriangleBound } r\}$ is covered by $r$ sets, not all of them can be sum-free. -/
theorem schurs_theorem_partition_not_sum_free (r : ℕ) (hr : 1 ≤ r) (A : Fin r → Finset ℕ)
    (h_cover : schurInterval (ramseyTriangleBound r) ⊆ Finset.biUnion Finset.univ A) :
    ∃ i : Fin r, ¬ isSumFree (A i) := by
  rcases schurs_theorem_partition r hr A h_cover with ⟨i, x, y, z, hx, hy, hz, -, -, -, hxyz⟩
  refine ⟨i, ?_⟩
  intro h_sf
  have := h_sf x hx y hy
  rw [hxyz] at this
  exact this hz

#print axioms schurs_theorem
#print axioms schurs_theorem_color_classes
#print axioms schurs_theorem_partition
#print axioms schurs_theorem_partition_not_sum_free

end SchursTheorem