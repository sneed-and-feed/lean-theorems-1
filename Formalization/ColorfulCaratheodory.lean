import Formalization.ColorfulCaratheodory.Basic
import Formalization.ColorfulCaratheodory.Separation
import Formalization.ColorfulCaratheodory.Perturbation
import Formalization.ColorfulCaratheodory.Transversals
import Formalization.ColorfulCaratheodory.Dim1
import Formalization.ColorfulCaratheodory.Selection
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Bárány's Colorful Carathéodory Theorem (1982) - Root Module

This module formalizes Bárány's Colorful Carathéodory Theorem, Selection Lemmas,
and the Centerpoint Theorem from first principles without custom axioms.

## Mathematical Framework (Bárány 1982)

Let $d \ge 0$.
* Ambient space: Euclidean vector space $\mathbb{R}^d$ modeled as `Fin d → ℝ`.
* Color classes: $d + 1$ sets $S_0, S_1, \dots, S_d \subset \mathbb{R}^d$.
* Colorful choice: A selection $x \in \prod_{i=0}^d S_i$, i.e. $x_i \in S_i$ for all $i \in \{0, \dots, d\}$.

## Main Results

1. `colorful_caratheodory_dim0`: Colorful Carathéodory in dimension $d = 0$.
2. `colorful_caratheodory_dim1`: Colorful Carathéodory in dimension $d = 1$.
3. `colorful_caratheodory_dim1_origin`: Colorful Carathéodory in dimension $d = 1$ centered at the origin.
4. `colorful_caratheodory_dim2`: Colorful Carathéodory in dimension $d = 2$.
5. `colorful_caratheodory_dim2_origin`: Colorful Carathéodory in dimension $d = 2$ centered at the origin.
6. `colorful_caratheodory_point`: Bárány's Colorful Carathéodory Theorem for general dimension $d$.
7. `colorful_caratheodory_origin`: Colorful Carathéodory Theorem centered at origin for general dimension $d$.
8. `caratheodory_classical`: Classical Carathéodory Theorem bound ($|T| \le d + 1$).
9. `caratheodory_classical_deduction`: Deduction of classical Carathéodory from colorful selection.
10. `centerpoint_1d`: 1D Centerpoint Theorem (median contains $\ge (|P|+1)/2$ points in each half-line).
11. `first_selection_lemma_1d`: Bárány's First Selection Lemma in dimension 1 ($\ge (|P|/2)(|P|-|P|/2)$ pairs).
12. `colorful_selection_lemma_1d`: Colorful Selection Lemma in dimension 1 (cross-product bounds & $\ge 1$ colorful pair).

## Reference
* I. Bárány, *A generalization of Carathéodory's theorem*, Discrete Mathematics 40 (1982), 141–152.
  https://doi.org/10.1016/0012-365X(82)90115-7
-/

open BigOperators Finset

noncomputable section

namespace ColorfulCaratheodory

variable {d : ℕ}

-- ============================================================================
-- Section 1: Core Definitions
-- ============================================================================

/-- Colorful choice predicate specialized to finsets. -/
def IsColorfulChoiceFinset (S : Fin (d + 1) → Finset (Fin d → ℝ)) (f : Fin (d + 1) → Fin d → ℝ) : Prop :=
  ∀ i : Fin (d + 1), f i ∈ S i

lemma isColorfulChoice_coe (S : Fin (d + 1) → Finset (Fin d → ℝ)) (f : Fin (d + 1) → Fin d → ℝ) :
    IsColorfulChoice (fun i ↦ (S i : Set (Fin d → ℝ))) f ↔ IsColorfulChoiceFinset S f :=
  Iff.rfl

lemma isColorfulChoiceFinset_iff_mem_transversals (S : Fin (d + 1) → Finset (Fin d → ℝ))
    (f : Fin (d + 1) → Fin d → ℝ) :
    IsColorfulChoiceFinset S f ↔ f ∈ colorfulTransversals S :=
  (mem_colorfulTransversals_iff S f).symm

/-- Bárány's Colorful Carathéodory Theorem statement:
If the target point $p$ is in the convex hull of each color class $S_i$,
then there exists a colorful choice $f$ whose convex hull contains $p$. -/
def ColorfulCaratheodoryStatement : Prop :=
  ∀ (d : ℕ) (S : Fin (d + 1) → Finset (Fin d → ℝ)) (p : Fin d → ℝ),
    (∀ i : Fin (d + 1), p ∈ convexHull ℝ (S i : Set (Fin d → ℝ))) →
      ∃ f : Fin (d + 1) → Fin d → ℝ,
        IsColorfulChoiceFinset S f ∧ p ∈ colorfulSimplex f

-- ============================================================================
-- Section 2: Classical Carathéodory Bound & Deduction
-- ============================================================================

/-- Cardinality bound for affine-independent subsets in `Fin d → ℝ`: any affine-independent
finset has cardinality at most $d + 1$. -/
lemma card_le_of_affineIndependent {d : ℕ} {T : Finset (Fin d → ℝ)}
    (h_aff : AffineIndependent ℝ ((↑) : T → (Fin d → ℝ))) :
    T.card ≤ d + 1 := by
  have h_le := AffineIndependent.card_le_finrank_succ h_aff
  have h_sub : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range ((↑) : T → Fin d → ℝ))) ≤ Module.finrank ℝ (Fin d → ℝ) := Submodule.finrank_le _
  have h_dim : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
  rw [Fintype.card_coe] at h_le
  omega

/-- **Classical Carathéodory Theorem (1907)**:
Any point $p \in \operatorname{conv}(S)$ in $\mathbb{R}^d$ can be expressed as a convex combination
of at most $d + 1$ points of $S$. -/
theorem caratheodory_classical (S_single : Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (hp : p ∈ convexHull ℝ S_single) :
    ∃ (T : Finset (Fin d → ℝ)), (T : Set (Fin d → ℝ)) ⊆ S_single ∧ T.card ≤ d + 1 ∧ p ∈ convexHull ℝ (T : Set (Fin d → ℝ)) :=
  ⟨Caratheodory.minCardFinsetOfMemConvexHull hp,
   Caratheodory.minCardFinsetOfMemConvexHull_subseteq hp,
   card_le_of_affineIndependent (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hp),
   Caratheodory.mem_minCardFinsetOfMemConvexHull hp⟩

/-- **Classical Carathéodory Theorem as a Deduction from Colorful Selection**:
Deduction of the classical Carathéodory bound $|T| \le d + 1$ from Bárány's colorful transversal selection.
Setting all $d + 1$ color classes to $S_{single}$, any colorful choice $f$ selects points from $S_{single}$,
and the range of $f$ has cardinality at most $d + 1$. -/
theorem caratheodory_classical_deduction (S_single : Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (_hp : p ∈ convexHull ℝ S_single)
    (h_colorful : ∃ f : Fin (d + 1) → Fin d → ℝ,
      IsColorfulChoice (fun _ ↦ S_single) f ∧ p ∈ colorfulSimplex f) :
    ∃ (T : Finset (Fin d → ℝ)), (T : Set (Fin d → ℝ)) ⊆ S_single ∧ T.card ≤ d + 1 ∧ p ∈ convexHull ℝ (T : Set (Fin d → ℝ)) := by
  obtain ⟨f, h_choice, h_conv⟩ := h_colorful
  let T : Finset (Fin d → ℝ) := Finset.univ.image f
  have hT_range : (T : Set (Fin d → ℝ)) = Set.range f := by
    ext y; simp only [T, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨T, by rw [hT_range]; rintro y ⟨i, rfl⟩; exact h_choice i,
    by simpa using Finset.card_image_le (s := Finset.univ) (f := f), ?_⟩
  rwa [colorfulSimplex, ← hT_range] at h_conv

lemma exists_subset_erase_of_not_injective {n m : ℕ} (f : Fin n → Fin m → ℝ)
    {q : Fin m → ℝ} (hq : q ∈ convexHull ℝ (Set.range f))
    (h_not_inj : ¬ Function.Injective f) :
    ∃ k : Fin n, q ∈ convexHull ℝ (f '' (Set.univ \ {k})) := by
  obtain ⟨i, j, hij_eq, hij_ne⟩ := Function.not_injective_iff.mp h_not_inj
  refine ⟨j, convexHull_mono ?_ hq⟩
  rintro y ⟨k, rfl⟩
  by_cases h : k = j
  · subst h; exact ⟨i, ⟨Set.mem_univ i, hij_ne⟩, hij_eq⟩
  · exact ⟨k, ⟨Set.mem_univ k, h⟩, rfl⟩

lemma exists_subset_erase_of_not_all {n m : ℕ} (f : Fin n → Fin m → ℝ)
    {q : Fin m → ℝ} (_hq : q ∈ convexHull ℝ (Set.range f))
    {T : Finset (Fin m → ℝ)} (hT_sub : (T : Set (Fin m → ℝ)) ⊆ Set.range f)
    (hT_mem : q ∈ convexHull ℝ (T : Set (Fin m → ℝ)))
    {k : Fin n} (hk : f k ∉ T) :
    ∃ j : Fin n, q ∈ convexHull ℝ (f '' (Set.univ \ {j})) := by
  refine ⟨k, convexHull_mono (fun y hy ↦ ?_) hT_mem⟩
  obtain ⟨m_idx, rfl⟩ := hT_sub hy
  exact ⟨m_idx, ⟨Set.mem_univ m_idx, fun h_eq ↦ hk (h_eq ▸ hy)⟩, rfl⟩

/-- If a point $q \in \operatorname{conv}(\operatorname{range} f)$ can be supported by at most $d$ points,
there exists a color index $k \in \operatorname{Fin}(d + 1)$ that is not needed to represent $q$,
so $q \in \operatorname{conv}(f '' (\operatorname{univ} \setminus \{k\}))$. -/
lemma exists_subset_erase_of_mem_convexHull {d : ℕ} (f : Fin (d + 1) → Fin d → ℝ)
    {q : Fin d → ℝ} (hq : q ∈ convexHull ℝ (Set.range f))
    (h_card : (Caratheodory.minCardFinsetOfMemConvexHull hq).card ≤ d) :
    ∃ k : Fin (d + 1), q ∈ convexHull ℝ (f '' (Set.univ \ {k})) := by
  let T := Caratheodory.minCardFinsetOfMemConvexHull hq
  have hT_sub := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hq
  have hT_mem := Caratheodory.mem_minCardFinsetOfMemConvexHull hq
  by_cases h_all : ∀ i : Fin (d + 1), f i ∈ T
  · have h_not_inj : ¬ Function.Injective f := fun h_inj ↦ by
      have h_card_univ : (Finset.univ.image f).card = d + 1 := by
        rw [Finset.card_image_of_injective _ h_inj, Finset.card_univ, Fintype.card_fin]
      have h_image_sub : Finset.univ.image f ⊆ T := by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact h_all i
      have h_le := (Finset.card_le_card h_image_sub).trans h_card
      omega
    exact exists_subset_erase_of_not_injective f hq h_not_inj
  · obtain ⟨k, hk⟩ : ∃ k, f k ∉ T := by contrapose! h_all; exact h_all
    exact exists_subset_erase_of_not_all f hq hT_sub hT_mem hk

/-- If a linear functional vanishes on a difference spanning set, it vanishes on the vectorSpan. -/
lemma dotProd_eq_zero_of_mem_vectorSpan {d : ℕ} {s : Set (Fin d → ℝ)} (v : Fin d → ℝ)
    (h_orth : ∀ x ∈ s, ∀ y ∈ s, dotProd v (x - y) = 0) :
    ∀ w ∈ vectorSpan ℝ s, dotProd v w = 0 := by
  intro w hw
  rw [vectorSpan_def] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact h_orth a ha b hb
  | zero => simp [dotProd_zero_right]
  | add x y _ _ ihx ihy => rw [dotProd_add_right, ihx, ihy, add_zero]
  | smul c x _ ih => rw [dotProd_smul_right, ih, mul_zero]

/-- If the vectorSpan of `s` is `⊤` and `v` is orthogonal to all differences in `s`, then `v = 0`. -/
lemma eq_zero_of_dotProd_vectorSpan_top {d : ℕ} {s : Set (Fin d → ℝ)} (v : Fin d → ℝ)
    (h_span : vectorSpan ℝ s = ⊤)
    (h_orth : ∀ x ∈ s, ∀ y ∈ s, dotProd v (x - y) = 0) :
    v = 0 := by
  have h_w : dotProd v v = 0 := by
    apply dotProd_eq_zero_of_mem_vectorSpan v h_orth
    rw [h_span]
    exact Submodule.mem_top
  exact (euclideanSq_eq_zero_iff v).mp h_w

/-- If `T` is an affinely independent subset of `Fin d → ℝ` with `card T = d + 1`, its vectorSpan is `⊤`. -/
lemma vectorSpan_eq_top_of_card_eq {d : ℕ} {T : Finset (Fin d → ℝ)}
    (h_aff : AffineIndependent ℝ ((↑) : T → (Fin d → ℝ)))
    (h_card : T.card = d + 1) :
    vectorSpan ℝ (T : Set (Fin d → ℝ)) = ⊤ := by
  have hc : Fintype.card T = Module.finrank ℝ (Fin d → ℝ) + 1 := by
    rw [Fintype.card_coe, h_card, Module.finrank_fin_fun]
  have h_top := AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one h_aff hc
  have h_range : Set.range ((↑) : T → Fin d → ℝ) = (T : Set (Fin d → ℝ)) := Subtype.range_coe
  rwa [h_range] at h_top

/-- First-order optimality condition: at a distance-minimizing point `q` in a convex hull,
the directional derivative towards any point `s` in the set is non-negative. -/
lemma dotProd_sub_nonneg_of_isMinOn {d : ℕ} {T : Finset (Fin d → ℝ)} {q p : Fin d → ℝ}
    (hq : q ∈ convexHull ℝ (T : Set (Fin d → ℝ)))
    (h_min : ∀ x ∈ convexHull ℝ (T : Set (Fin d → ℝ)), euclideanSq (q - p) ≤ euclideanSq (x - p))
    (s : Fin d → ℝ) (hs : s ∈ T) :
    0 ≤ dotProd (q - p) (s - q) := by
  by_contra! h_neg
  let v := q - p; let u := s - q
  have hu_nonneg : 0 ≤ euclideanSq u := euclideanSq_nonneg u
  have hdenom : 0 < euclideanSq u + 1 := by linarith
  let ε := (- dotProd v u) / (euclideanSq u + 1)
  have hε_pos : 0 < ε := div_pos (by linarith) hdenom
  let ε' := min (1 / 2) ε
  have hε'_pos : 0 < ε' := lt_min (by norm_num) hε_pos
  have hε'_le_half : ε' ≤ 1 / 2 := min_le_left _ _
  have hε'_le_ε : ε' ≤ ε := min_le_right _ _
  have hε'_lt1 : ε' < 1 := by linarith
  let y := (1 - ε') • q + ε' • s
  have hy_mem : y ∈ convexHull ℝ (T : Set (Fin d → ℝ)) := by
    exact convex_convexHull ℝ (T : Set (Fin d → ℝ)) hq (subset_convexHull ℝ _ hs) (by linarith) (by linarith) (by ring)
  have hy_dist : euclideanSq (y - p) < euclideanSq (q - p) := by
    have h_comb : y - p = v + ε' • u := by
      ext i; simp only [y, v, u, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have h_exp : euclideanSq (y - p) = euclideanSq v + 2 * ε' * dotProd v u + ε' ^ 2 * euclideanSq u := by
      rw [h_comb]
      simp only [euclideanSq, dotProd_add_left, dotProd_add_right, dotProd_smul_left, dotProd_smul_right, dotProd_comm u v]
      ring
    rw [h_exp]
    have h1 : 2 * ε' * dotProd v u + ε' ^ 2 * euclideanSq u < 0 := by
      have : ε' * (2 * dotProd v u + ε' * euclideanSq u) < 0 := by
        apply mul_neg_of_pos_of_neg hε'_pos
        have h_le : ε' * euclideanSq u ≤ ε * euclideanSq u := mul_le_mul_of_nonneg_right hε'_le_ε hu_nonneg
        have h_eps_val : ε * euclideanSq u < - dotProd v u := by
          dsimp [ε]; rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom]
          nlinarith [show 0 < - dotProd v u by linarith]
        linarith
      linarith
    linarith
  have h_le := h_min y hy_mem
  linarith

lemma exists_erase_mem_convexHull_of_isMinOn {d : ℕ} {T : Finset (Fin d → ℝ)} {q p : Fin d → ℝ}
    (hq : q ∈ convexHull ℝ (T : Set (Fin d → ℝ)))
    (h_min : ∀ x ∈ convexHull ℝ (T : Set (Fin d → ℝ)), euclideanSq (q - p) ≤ euclideanSq (x - p))
    (h_aff : AffineIndependent ℝ ((↑) : T → (Fin d → ℝ)))
    (h_card : T.card = d + 1)
    (hne : q ≠ p) :
    ∃ s ∈ T, q ∈ convexHull ℝ ((T.erase s : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) := by
  obtain ⟨w, hw_nonneg, hw_sum, hq_cm⟩ := Finset.mem_convexHull.mp hq
  have hq_eq : ∑ y ∈ T, w y • y = q := by dsimp [centerMass] at hq_cm; rwa [hw_sum, inv_one, one_smul] at hq_cm
  have h_nonneg_dot : ∀ s ∈ T, 0 ≤ dotProd (q - p) (s - q) := fun s hs ↦ dotProd_sub_nonneg_of_isMinOn hq h_min s hs
  by_cases h_exists_zero : ∃ s ∈ T, w s = 0
  · obtain ⟨s, hs, hw_s⟩ := h_exists_zero
    refine ⟨s, hs, Finset.mem_convexHull.mpr ?_⟩
    have hw'_sum : ∑ y ∈ T.erase s, w y = 1 := by
      have := (Finset.sum_erase_add T w hs).symm
      rwa [hw_s, add_zero, hw_sum, eq_comm] at this
    have hq'_cm : q = (T.erase s).centerMass w id := by
      dsimp [centerMass]
      rw [hw'_sum, inv_one, one_smul]
      have := (Finset.sum_erase_add T (fun y ↦ w y • y) hs).symm
      rwa [hw_s, zero_smul, add_zero, hq_eq] at this
    exact ⟨w, fun y hy ↦ hw_nonneg y (Finset.mem_of_mem_erase hy), hw'_sum, hq'_cm.symm⟩
  · have h_pos_w : ∀ s ∈ T, 0 < w s := fun s hs ↦ lt_of_le_of_ne (hw_nonneg s hs) (fun h ↦ h_exists_zero ⟨s, hs, h.symm⟩)
    have h_dot_zero : ∀ s ∈ T, dotProd (q - p) (s - q) = 0 := by
      intro s hs
      by_contra! h_gt
      have h_term_pos : 0 < w s * dotProd (q - p) (s - q) := mul_pos (h_pos_w s hs) (lt_of_le_of_ne (h_nonneg_dot s hs) h_gt.symm)
      have h_sum_pos : 0 < ∑ y ∈ T, w y * dotProd (q - p) (y - q) :=
        h_term_pos.trans_le (single_le_sum (fun y hy ↦ mul_nonneg (hw_nonneg y hy) (h_nonneg_dot y hy)) hs)
      have h_zero : ∑ y ∈ T, w y * dotProd (q - p) (y - q) = 0 := by
        rw [← dotProd_sum_smul_right, sum_smul_sub_eq_zero hw_sum hq_eq, dotProd_zero_right]
      linarith
    have h_orth : ∀ x ∈ (T : Set (Fin d → ℝ)), ∀ y ∈ (T : Set (Fin d → ℝ)), dotProd (q - p) (x - y) = 0 := by
      intro x hx y hy
      have : x - y = (x - q) - (y - q) := by simp
      rw [this, dotProd_sub_right, h_dot_zero x hx, h_dot_zero y hy, sub_self]
    have h_top : vectorSpan ℝ (T : Set (Fin d → ℝ)) = ⊤ := vectorSpan_eq_top_of_card_eq h_aff h_card
    have h_qp_zero : q - p = 0 := eq_zero_of_dotProd_vectorSpan_top (q - p) h_top h_orth
    exact False.elim (hne (sub_eq_zero.mp h_qp_zero))

-- ============================================================================
-- Section 3: Low-Dimensional Colorful Carathéodory Theorems
-- ============================================================================

/-- **Colorful Carathéodory Theorem in Dimension 0**:
In dimension $0$, the ambient space `Fin 0 → ℝ` consists of a single point $0$.
Any non-empty color class $S_0$ trivially contains the target point $p = 0$. -/
theorem colorful_caratheodory_dim0 (S : Fin 1 → Set (Fin 0 → ℝ)) (p : Fin 0 → ℝ)
    (hp : ∀ i : Fin 1, p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 1 → Fin 0 → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := by
  have ⟨x, hx⟩ : (S 0).Nonempty := convexHull_nonempty_iff.mp ⟨p, hp 0⟩
  refine ⟨fun _ ↦ x, fun i ↦ by fin_cases i; exact hx, ?_⟩
  rw [Subsingleton.elim p x]
  exact subset_convexHull ℝ _ ⟨0, rfl⟩

/-- **Colorful Carathéodory Theorem in Dimension 1 (Origin Form)**:
Specialization to dimension $d = 1$ centered at the origin. -/
theorem colorful_caratheodory_dim1_origin (S : Fin 2 → Set (Fin 1 → ℝ))
    (h_origin : ∀ i : Fin 2, (0 : Fin 1 → ℝ) ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 2 → Fin 1 → ℝ, IsColorfulChoice S f ∧ (0 : Fin 1 → ℝ) ∈ colorfulSimplex f :=
  colorful_caratheodory_dim1 S 0 h_origin

/-- Helper: If the target point $p$ belongs directly to one of the color classes $S_j$,
a colorful transversal containing $p$ is immediately constructed by selecting $p$ at color $j$
and arbitrary witnesses at all other colors. -/
lemma colorful_caratheodory_of_mem (S : Fin (d + 1) → Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (hp_conv : ∀ i : Fin (d + 1), p ∈ convexHull ℝ (S i))
    (j : Fin (d + 1)) (hp_mem : p ∈ S j) :
    ∃ f : Fin (d + 1) → Fin d → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := by
  have h_nonempty : ∀ i : Fin (d + 1), (S i).Nonempty := fun i ↦ convexHull_nonempty_iff.mp ⟨p, hp_conv i⟩
  choose g hg using h_nonempty
  refine ⟨fun i ↦ if h : i = j then p else g i, fun i ↦ by dsimp; split_ifs with hij <;> [subst hij; skip] <;> [exact hp_mem; exact hg i], ?_⟩
  exact subset_convexHull ℝ _ ⟨j, by simp⟩

-- ============================================================================
-- Section 4: General Dimension Colorful Carathéodory
-- ============================================================================

/-- **Bárány's Colorful Carathéodory Theorem (General Point Form, 1982)**:
Let $S_0, \dots, S_d \subset \mathbb{R}^d$ be $d+1$ sets of points such that a target point
$p \in \mathbb{R}^d$ belongs to the convex hull of each set:
$$p \in \operatorname{conv}(S_i) \quad \text{for all } i \in \{0, 1, \dots, d\}.$$
Then there exists a colorful choice $f$ ($f(i) \in S_i$ for each $i$) such that $p$ lies
in the colorful simplex formed by $f$:
$$p \in \operatorname{conv}(\operatorname{range} f) = \operatorname{conv}(\{f(0), \dots, f(d)\}).$$ -/
theorem colorful_caratheodory_point (S : Fin (d + 1) → Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (hp : ∀ i : Fin (d + 1), p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin (d + 1) → Fin d → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := by
  let F : Fin (d + 1) → Finset (Fin d → ℝ) := fun i ↦ Caratheodory.minCardFinsetOfMemConvexHull (hp i)
  have hF_sub : ∀ i, (F i : Set (Fin d → ℝ)) ⊆ S i := fun i ↦ Caratheodory.minCardFinsetOfMemConvexHull_subseteq (hp i)
  have hF_mem : ∀ i, p ∈ convexHull ℝ (F i : Set (Fin d → ℝ)) := fun i ↦ Caratheodory.mem_minCardFinsetOfMemConvexHull (hp i)
  have hChoice : Nonempty (ColorfulChoice F) :=
    (colorfulChoice_nonempty_iff F).mpr (fun i ↦ Caratheodory.minCardFinsetOfMemConvexHull_nonempty (hp i))
  have hChoice_univ : (Finset.univ : Finset (ColorfulChoice F)).Nonempty := ⟨Classical.choice hChoice, Finset.mem_univ _⟩
  have h_witness : ∀ c : ColorfulChoice F, ∃ q ∈ convexHull ℝ (Set.range c.val),
      ∀ x ∈ convexHull ℝ (Set.range c.val), euclideanSq (q - p) ≤ euclideanSq (x - p) := fun c ↦ by
    have h_cont : Continuous (fun x ↦ euclideanSq (x - p)) := by
      simp only [euclideanSq_eq_sum_sq]
      exact continuous_finsetSum Finset.univ (fun i _ ↦ ((continuous_apply i).sub continuous_const).pow 2)
    exact (Set.finite_range c.val).isCompact_convexHull ℝ |>.exists_isMinOn ⟨c.val 0, subset_convexHull ℝ _ ⟨0, rfl⟩⟩ h_cont.continuousOn
  let closest (c : ColorfulChoice F) : Fin d → ℝ := Classical.choose (h_witness c)
  have closest_mem (c : ColorfulChoice F) : closest c ∈ convexHull ℝ (Set.range c.val) := (Classical.choose_spec (h_witness c)).1
  have closest_min (c : ColorfulChoice F) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ (Set.range c.val)) :
      euclideanSq (closest c - p) ≤ euclideanSq (x - p) := (Classical.choose_spec (h_witness c)).2 x hx
  obtain ⟨best, -, hbest⟩ := Finset.exists_min_image (Finset.univ : Finset (ColorfulChoice F)) (fun c ↦ euclideanSq (closest c - p)) hChoice_univ
  let f_best := best.val
  refine ⟨f_best, fun i ↦ hF_sub i (best.val_mem i), ?_⟩
  dsimp [colorfulSimplex, f_best]
  by_contra h_not_in
  have h_closest_ne_p : closest best ≠ p := fun h_eq ↦ h_not_in (h_eq ▸ closest_mem best)
  have hq_mem := closest_mem best
  have h_unused : ∃ k : Fin (d + 1), closest best ∈ convexHull ℝ (f_best '' (Set.univ \ {k})) := by
    let T := Caratheodory.minCardFinsetOfMemConvexHull hq_mem
    have hT_sub : (T : Set (Fin d → ℝ)) ⊆ Set.range f_best := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hq_mem
    have hT_mem : closest best ∈ convexHull ℝ (T : Set (Fin d → ℝ)) := Caratheodory.mem_minCardFinsetOfMemConvexHull hq_mem
    have h_aff := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hq_mem
    rcases lt_or_eq_of_le (card_le_of_affineIndependent h_aff) with h_lt | h_eq
    · exact exists_subset_erase_of_mem_convexHull f_best hq_mem (Nat.le_of_lt_succ h_lt)
    · have h_min_T : ∀ x ∈ convexHull ℝ (T : Set (Fin d → ℝ)), euclideanSq (closest best - p) ≤ euclideanSq (x - p) :=
        fun x hx ↦ closest_min best x (convexHull_mono hT_sub hx)
      obtain ⟨s, hs, hq_erase⟩ := exists_erase_mem_convexHull_of_isMinOn hT_mem h_min_T h_aff h_eq h_closest_ne_p
      obtain ⟨m_idx, rfl⟩ := hT_sub hs
      have hs_not_in : f_best m_idx ∉ T.erase (f_best m_idx) := Finset.notMem_erase (f_best m_idx) T
      have h_sub_erase : ((T.erase (f_best m_idx) : Finset (Fin d → ℝ)) : Set (Fin d → ℝ)) ⊆ Set.range f_best :=
        (Finset.coe_subset.mpr (Finset.erase_subset _ _)).trans hT_sub
      exact exists_subset_erase_of_not_all f_best hq_mem h_sub_erase hq_erase hs_not_in
  obtain ⟨k, hk_erase⟩ := h_unused
  obtain ⟨s, hs, hdot_s⟩ := exists_nonpos_dotProd_of_mem_convexHull (hF_mem k) (closest best - p)
  let replacement := updateColorfulChoice best k s hs
  obtain ⟨y, ε, hε0, hε1, hy_eq, hy_lt⟩ := exists_closer_point_on_segment p (closest best) s h_closest_ne_p hdot_s
  have hy_mem_replacement : y ∈ convexHull ℝ (Set.range replacement.val) := by
    rw [hy_eq, range_updateColorfulChoice]
    exact segment_mem_convexHull_insert s (f_best '' (Set.univ \ {k})) (closest best) hk_erase (le_of_lt hε0) (le_of_lt hε1)
  have h_closest_repl := closest_min replacement y hy_mem_replacement
  have h_best_le := hbest replacement (Finset.mem_univ replacement)
  linarith

/-- **Bárány's Colorful Carathéodory Theorem (Origin Form, 1982)**:
If the origin $0 \in \mathbb{R}^d$ belongs to the convex hull of each of the $d + 1$
color classes $S_i \subset \mathbb{R}^d$, then there exists a colorful choice $f$
such that $0 \in \operatorname{conv}(\operatorname{range} f)$. -/
theorem colorful_caratheodory_origin (S : Fin (d + 1) → Set (Fin d → ℝ))
    (h_origin : ∀ i : Fin (d + 1), (0 : Fin d → ℝ) ∈ convexHull ℝ (S i)) :
    ∃ f : Fin (d + 1) → Fin d → ℝ, IsColorfulChoice S f ∧ (0 : Fin d → ℝ) ∈ colorfulSimplex f :=
  colorful_caratheodory_point S 0 h_origin

/-- **Colorful Carathéodory Theorem in Dimension 2 (Colorful Triangle Theorem)**:
For any three color classes $S_0, S_1, S_2 \subset \mathbb{R}^2$ whose convex hulls all contain $p$,
there exists a colorful transversal $f$ ($f(0) \in S_0, f(1) \in S_1, f(2) \in S_2$)
such that $p \in \operatorname{conv}(\operatorname{range} f)$. -/
theorem colorful_caratheodory_dim2 (S : Fin 3 → Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ)
    (hp : ∀ i : Fin 3, p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 3 → Fin 2 → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f :=
  colorful_caratheodory_point S p hp

/-- Specialization to dimension $d = 2$ centered at the origin. -/
theorem colorful_caratheodory_dim2_origin (S : Fin 3 → Set (Fin 2 → ℝ))
    (h_origin : ∀ i : Fin 3, (0 : Fin 2 → ℝ) ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 3 → Fin 2 → ℝ, IsColorfulChoice S f ∧ (0 : Fin 2 → ℝ) ∈ colorfulSimplex f :=
  colorful_caratheodory_origin S h_origin

-- ============================================================================
-- Section 5: Selection Lemmas and Centerpoints in Dimension 1
-- ============================================================================

#check centerpoint_1d
#check first_selection_lemma_1d
#check colorful_selection_lemma_1d

#print axioms colorful_caratheodory_dim0
#print axioms colorful_caratheodory_dim1
#print axioms colorful_caratheodory_dim2
#print axioms colorful_caratheodory_point
#print axioms colorful_caratheodory_origin
#print axioms caratheodory_classical
#print axioms caratheodory_classical_deduction
#print axioms centerpoint_1d
#print axioms first_selection_lemma_1d
#print axioms colorful_selection_lemma_1d

end ColorfulCaratheodory