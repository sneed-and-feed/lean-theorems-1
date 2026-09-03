import Formalization.TverbergsTheorem.Basis
import Formalization.TverbergsTheorem.Dim1
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# One-Dimensional Colorful Tverberg Theorem for Arbitrary $r$

This module formalizes the 1-dimensional Colorful Tverberg Theorem for arbitrary $r \ge 1$.

## Mathematical Summary
Given two disjoint color classes $C_0, C_1 \subset \mathbb{R}^1$, each of cardinality $r$,
sorting $C_0$ as $x_0 < x_1 < \dots < x_{r-1}$ and $C_1$ as $y_0 < y_1 < \dots < y_{r-1}$,
we pair $x_i \in C_0$ with $y_{r-1-i} \in C_1$.
The intervals $I_i = [\min(x_i, y_{r-1-i}), \max(x_i, y_{r-1-i})]$ pairwise intersect because
for any $i, k$, $\min(x_i, y_{r-1-i}) \le \max(x_k, y_{r-1-k})$.
By Helly's property in dimension 1 (or taking $M = \max_i \min(x_i, y_{r-1-i})$), the point $M$
lies in all intervals, providing a common point in the convex hulls of all $r$ colorful pairs.

## Main Theorems
* `colorful_tverberg_1d`: 1-dimensional Colorful Tverberg theorem for 2 color classes of size $r$.

## References
* I. Bárány, D. G. Larman, and J. Pach (1992), *Radon-partition property in topological affine spaces*,
  Amer. Math. Monthly 99(5):422–431.
* J. Matoušek (2002), *Lectures on Discrete Geometry*, GTM 212, Springer, §8.4.
-/

namespace TverbergsTheorem

open Finset BigOperators

/-- **1-Dimensional Colorful Tverberg Theorem for Arbitrary r (Bárány–Larman–Pach 1992 / d = 1)**:
Given two disjoint color classes of r points each in ℝ¹, they can be partitioned into r disjoint
colorful pairs (each containing 1 point from C₀ and 1 point from C₁) whose convex hulls share
a common point of intersection. -/
theorem colorful_tverberg_1d (r : ℕ) (hr : 1 ≤ r)
    (C₀ C₁ : Finset (Fin 1 → ℝ)) (h₀ : C₀.card = r) (h₁ : C₁.card = r)
    (h_disj : Disjoint C₀ C₁) :
    ∃ P : Fin r → Finset (Fin 1 → ℝ),
      (∀ i, (P i).card = 2) ∧
      (∀ i, ∃ x ∈ C₀, ∃ y ∈ C₁, P i = {x, y}) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (Finset.biUnion Finset.univ P = C₀ ∪ C₁) ∧
      (⋂ i : Fin r, convexHull ℝ (P i : Set (Fin 1 → ℝ))).Nonempty := by
  classical
  have hcoord_inj : Function.Injective (· 0 : (Fin 1 → ℝ) → ℝ) := fun x y h ↦ funext fun ⟨0, _⟩ ↦ h

  let T₀ : Finset ℝ := C₀.image (· 0)
  have hT₀_card : T₀.card = r := by rw [Finset.card_image_of_injective C₀ hcoord_inj, h₀]
  let q₀ : Fin r ↪o ℝ := T₀.orderEmbOfFin hT₀_card
  let x₀ : Fin r → Fin 1 → ℝ := fun i _ ↦ q₀ i

  let T₁ : Finset ℝ := C₁.image (· 0)
  have hT₁_card : T₁.card = r := by rw [Finset.card_image_of_injective C₁ hcoord_inj, h₁]
  let q₁ : Fin r ↪o ℝ := T₁.orderEmbOfFin hT₁_card
  let x₁ : Fin r → Fin 1 → ℝ := fun i _ ↦ q₁ i

  have hx₀_inj : Function.Injective x₀ := fun _ _ h ↦ q₀.injective (congr_fun h 0)
  have hx₁_inj : Function.Injective x₁ := fun _ _ h ↦ q₁.injective (congr_fun h 0)

  have hx₀_mem : ∀ i, x₀ i ∈ C₀ := fun i ↦ by
    obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp (T₀.orderEmbOfFin_mem hT₀_card i)
    rwa [show x₀ i = y from funext fun ⟨0, _⟩ ↦ hyq.symm]

  have hx₁_mem : ∀ i, x₁ i ∈ C₁ := fun i ↦ by
    obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp (T₁.orderEmbOfFin_mem hT₁_card i)
    rwa [show x₁ i = y from funext fun ⟨0, _⟩ ↦ hyq.symm]

  have hx₀_surj : ∀ y ∈ C₀, ∃ i, x₀ i = y := fun y hy ↦ by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (by rw [T₀.image_orderEmbOfFin_univ hT₀_card]; exact Finset.mem_image_of_mem _ hy)
    exact ⟨i, funext fun ⟨0, _⟩ ↦ hi⟩

  have hx₁_surj : ∀ y ∈ C₁, ∃ i, x₁ i = y := fun y hy ↦ by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (by rw [T₁.image_orderEmbOfFin_univ hT₁_card]; exact Finset.mem_image_of_mem _ hy)
    exact ⟨i, funext fun ⟨0, _⟩ ↦ hi⟩

  let j_fn : Fin r → Fin r := fun i ↦ ⟨r - 1 - i.1, by omega⟩
  have hj_invol : ∀ i, j_fn (j_fn i) = i := fun i ↦ Fin.ext (by dsimp [j_fn]; omega)
  have hj_inj : Function.Injective j_fn := fun a b h ↦ by rw [← hj_invol a, h, hj_invol]
  have hj_surj : Function.Surjective j_fn := fun i ↦ ⟨j_fn i, hj_invol i⟩

  have h_ne_colors : ∀ i k, x₀ i ≠ x₁ k := fun i k h ↦
    Finset.disjoint_left.mp h_disj (hx₀_mem i) (h ▸ hx₁_mem k)

  let P : Fin r → Finset (Fin 1 → ℝ) := fun i ↦ {x₀ i, x₁ (j_fn i)}
  have hP_card : ∀ i, (P i).card = 2 := fun i ↦ Finset.card_pair (h_ne_colors i (j_fn i))
  have hP_colors : ∀ i, ∃ x ∈ C₀, ∃ y ∈ C₁, P i = {x, y} :=
    fun i ↦ ⟨x₀ i, hx₀_mem i, x₁ (j_fn i), hx₁_mem (j_fn i), rfl⟩

  have hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
    intro i k hik; rw [Finset.disjoint_iff_ne]; rintro u hu v hv rfl
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with heq | heq
    · exact hik (hx₀_inj heq)
    · exact (h_ne_colors i _ heq).elim
    · exact (h_ne_colors k _ heq.symm).elim
    · exact hik (hj_inj (hx₁_inj heq))

  have hP_union : Finset.biUnion Finset.univ P = C₀ ∪ C₁ := by
    ext z; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, P, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl | rfl⟩ <;> [exact Or.inl (hx₀_mem i); exact Or.inr (hx₁_mem _)]
    · rintro (hz | hz)
      · obtain ⟨i, rfl⟩ := hx₀_surj z hz; exact ⟨i, Or.inl rfl⟩
      · obtain ⟨k, rfl⟩ := hx₁_surj z hz; obtain ⟨i, rfl⟩ := hj_surj k; exact ⟨i, Or.inr rfl⟩

  have hab_le : ∀ i k : Fin r, min (q₀ i) (q₁ (j_fn i)) ≤ max (q₀ k) (q₁ (j_fn k)) := by
    intro i k; rcases le_total i.1 k.1 with hik | hik
    · exact (min_le_left _ _).trans ((q₀.monotone hik).trans (le_max_left _ _))
    · exact (min_le_right _ _).trans ((q₁.monotone (show (j_fn i).1 ≤ (j_fn k).1 by dsimp [j_fn]; omega)).trans (le_max_right _ _))

  let A : Finset ℝ := Finset.univ.image (fun i ↦ min (q₀ i) (q₁ (j_fn i)))
  have hA_nonempty : A.Nonempty := ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hr⟩)⟩
  let M : ℝ := A.max' hA_nonempty
  have hM_ge : ∀ i, min (q₀ i) (q₁ (j_fn i)) ≤ M := fun i ↦ Finset.le_max' A _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hM_le : ∀ k, M ≤ max (q₀ k) (q₁ (j_fn k)) := fun k ↦ by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.max'_mem A hA_nonempty)
    dsimp [M]; rw [← hi]; exact hab_le i k

  have hp_mem (i : Fin r) : (fun _ ↦ M : Fin 1 → ℝ) ∈ convexHull ℝ (P i : Set (Fin 1 → ℝ)) := by
    rw [show (P i : Set (Fin 1 → ℝ)) = {x₀ i, x₁ (j_fn i)} by simp [P]]
    have ha := hM_ge i; have hb := hM_le i
    rcases le_total (q₀ i) (q₁ (j_fn i)) with h | h
    · rw [min_eq_left h] at ha; rw [max_eq_right h] at hb
      exact mem_convexHull_pair_1d (x₀ i) (x₁ (j_fn i)) (fun _ ↦ M) ha hb
    · rw [min_eq_right h] at ha; rw [max_eq_left h] at hb
      rw [Set.pair_comm]
      exact mem_convexHull_pair_1d (x₁ (j_fn i)) (x₀ i) (fun _ ↦ M) ha hb

  exact ⟨P, hP_card, hP_colors, hP_disj, hP_union, ⟨fun _ ↦ M, Set.mem_iInter.mpr hp_mem⟩⟩

end TverbergsTheorem
