import Formalization.TverbergsTheorem.Basis
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
# One-Dimensional Tverberg Theorem for Arbitrary $r$

This module formalizes the complete proof of Tverberg's theorem in dimension $d = 1$
for all $r \ge 1$ via sorted order embeddings, median selection, and symmetric pairing.

## Mathematical Summary
Given a set $S \subset \mathbb{R}^1$ of $2r - 1$ points, sorting the points yields
$x_0 < x_1 < \dots < x_{2r-2}$. The median element $x_{r-1}$ forms a singleton block,
and each other block is formed by symmetric pairs $\{x_c, x_{2r-2-c}\}$ for $0 \le c < r-1$.
Since $x_c \le x_{r-1} \le x_{2r-2-c}$, the median lies in the convex hull of every block.

## Main Theorems
* `mem_convexHull_pair_1d`: A 1D point between two endpoints lies in their convex hull.
* `tverberg_1d`: Exact 1D Tverberg theorem for $|S| = 2r - 1$.
* `tverberg_1d_of_card_ge`: Monotone 1D Tverberg theorem for $|S| \ge 2r - 1$.

## References
* H. Tverberg (1966), *A generalization of Radon's theorem*, J. London Math. Soc. 41:123–128.
* W. Mulzer and D. Werner (2013), *Approximating Tverberg points in linear time for any fixed dimension*,
  Discrete Comput. Geom. 50:520–535, §2.2.
-/

namespace TverbergsTheorem

open Finset BigOperators

/-- In 1 dimension (ℝ¹), any point between two endpoints lies in their convex hull. -/
lemma mem_convexHull_pair_1d (u v m : Fin 1 → ℝ) (h1 : u 0 ≤ m 0) (h2 : m 0 ≤ v 0) :
    m ∈ convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) := by
  by_cases huv : u 0 = v 0
  · have : u = m := funext fun ⟨0, _⟩ ↦ by change u 0 = m 0; linarith
    subst this; exact subset_convexHull ℝ _ (Set.mem_insert u {v})
  · have h_denom : 0 < v 0 - u 0 := by have : u 0 < v 0 := lt_of_le_of_ne (le_trans h1 h2) huv; linarith
    let a := (v 0 - m 0) / (v 0 - u 0)
    let b := (m 0 - u 0) / (v 0 - u 0)
    have hab : a + b = 1 := by
      dsimp [a, b]; rw [← add_div, show v 0 - m 0 + (m 0 - u 0) = v 0 - u 0 by ring, div_self (ne_of_gt h_denom)]
    have hm_comb : a • u + b • v = m := by
      funext ⟨0, _⟩; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; dsimp [a, b]; field_simp; ring
    have hu : u ∈ convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) := subset_convexHull ℝ _ (Set.mem_insert u _)
    have hv : v ∈ convexHull ℝ ({u, v} : Set (Fin 1 → ℝ)) := subset_convexHull ℝ _ (Set.mem_insert_of_mem u (Set.mem_singleton v))
    rw [← hm_comb]
    exact convex_convexHull ℝ _ hu hv (div_nonneg (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith)) hab

/-- **1-Dimensional Tverberg Theorem for Arbitrary r (1966):**
    Any set S of 2r - 1 points in ℝ¹ can be partitioned into r subsets whose convex hulls
    share a common point of intersection. -/
theorem tverberg_1d (r : ℕ) (hr : 1 ≤ r)
    (S : Finset (Fin 1 → ℝ)) (hS : S.card = (r - 1) * (1 + 1) + 1) :
    ∃ P : Fin r → Finset (Fin 1 → ℝ), IsTverbergPartition S P := by
  classical
  let N := 2 * r - 1
  have hS_N : S.card = N := by dsimp [N]; omega
  let coord : (Fin 1 → ℝ) → ℝ := fun x ↦ x 0
  have hcoord_inj : Function.Injective coord := fun _ _ h ↦ funext fun ⟨0, _⟩ ↦ h
  let T : Finset ℝ := S.image coord
  have hT_card : T.card = N := by rw [Finset.card_image_of_injective S hcoord_inj, hS_N]
  let q : Fin N ↪o ℝ := T.orderEmbOfFin hT_card
  let x : Fin N → Fin 1 → ℝ := fun i _ ↦ q i
  have hx_inj : Function.Injective x := fun i j hij ↦ q.injective (congr_fun hij 0)
  have hx_mem : ∀ i : Fin N, x i ∈ S := fun i ↦ by
    obtain ⟨y, hyS, hyq⟩ := Finset.mem_image.mp (T.orderEmbOfFin_mem hT_card i)
    rwa [show x i = y from funext fun ⟨0, _⟩ ↦ hyq.symm]
  have hx_surj : ∀ y ∈ S, ∃ i : Fin N, x i = y := fun y hyS ↦ by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (by rw [T.image_orderEmbOfFin_univ hT_card]; exact Finset.mem_image_of_mem _ hyS)
    exact ⟨i, funext fun ⟨0, _⟩ ↦ hi⟩
  have hmed : r - 1 < N := by dsimp [N]; omega
  let med : Fin N := ⟨r - 1, hmed⟩
  let lower : Fin r → Fin N := fun c ↦ ⟨c.1, by dsimp [N]; omega⟩
  let upper : Fin r → Fin N := fun c ↦ ⟨2 * r - 2 - c.1, by dsimp [N]; omega⟩
  let I : Fin r → Finset (Fin N) := fun c ↦ if c.1 = r - 1 then {med} else {lower c, upper c}
  let P : Fin r → Finset (Fin 1 → ℝ) := fun c ↦ (I c).image x
  have hI_val : ∀ (c : Fin r) (a : Fin N), a ∈ I c → min a.1 (2 * r - 2 - a.1) = c.1 := by
    intro c a ha; dsimp [I] at ha; split_ifs at ha with hc
    · simp only [Finset.mem_singleton] at ha; subst ha; dsimp [med]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl <;> (dsimp [lower, upper]; omega)
  have hI_unique (i j : Fin r) (a : Fin N) (hai : a ∈ I i) (haj : a ∈ I j) : i = j :=
    Fin.ext ((hI_val i a hai).symm.trans (hI_val j a haj))
  have hI_cover : ∀ a : Fin N, ∃ c : Fin r, a ∈ I c := by
    intro a
    by_cases halow : a.1 < r - 1
    · exact ⟨⟨a.1, by omega⟩, by simp [I, show a.1 ≠ r - 1 by omega, lower]⟩
    · by_cases hamid : a.1 = r - 1
      · refine ⟨⟨r - 1, by omega⟩, by simp [I, med, show a = med from Fin.ext (by dsimp [med]; exact hamid)]⟩
      · have : 2 * r - 2 - a.1 < r := by have := a.2; dsimp [N] at this; omega
        have hc_ne : 2 * r - 2 - a.1 ≠ r - 1 := by omega
        refine ⟨⟨2 * r - 2 - a.1, this⟩, ?_⟩
        simp only [I, hc_ne, ite_false, Finset.mem_insert, Finset.mem_singleton]
        right
        exact Fin.ext (by dsimp [upper]; omega)
  refine ⟨P, fun c y hy ↦ by obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy; exact hx_mem i,
    fun i j hij ↦ by
      rw [Finset.disjoint_iff_ne]; rintro y1 hy1 y2 hy2 rfl
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy1
      obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hy2
      exact hij (hI_unique i j a ha (hx_inj heq ▸ hb)),
    ?_,
    ⟨x med, Set.mem_iInter.mpr fun c ↦ ?_⟩⟩
  · ext y
    constructor
    · intro hy; obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hy; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc; exact hx_mem i
    · intro hy
      obtain ⟨i, rfl⟩ := hx_surj y hy
      obtain ⟨c, hic⟩ := hI_cover i
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, Finset.mem_image.mpr ⟨i, hic, rfl⟩⟩
  · by_cases hclast : c.1 = r - 1
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨med, by simp [I, hclast], rfl⟩))
    · have hlo : x (lower c) 0 ≤ x med 0 := q.monotone (show (lower c).1 ≤ med.1 by dsimp [lower, med]; omega)
      have hhi : x med 0 ≤ x (upper c) 0 := q.monotone (show med.1 ≤ (upper c).1 by dsimp [upper, med]; omega)
      simpa [P, I, hclast] using mem_convexHull_pair_1d (x (lower c)) (x (upper c)) (x med) hlo hhi

/-- **Monotone one-dimensional Tverberg theorem.**
Any finite set of at least `2 * r - 1` points in ℝ¹ admits a Tverberg partition
into `r` blocks covering the entire set. -/
theorem tverberg_1d_of_card_ge (r : ℕ) (hr : 1 ≤ r)
    (S : Finset (Fin 1 → ℝ)) (hS : (r - 1) * (1 + 1) + 1 ≤ S.card) :
    ∃ P : Fin r → Finset (Fin 1 → ℝ), IsTverbergPartition S P := by
  obtain ⟨T, hTS, hT_card⟩ := Finset.exists_subset_card_eq hS
  obtain ⟨P, hP⟩ := tverberg_1d r hr T hT_card
  exact hP.extend_superset hr hTS

end TverbergsTheorem
