import Formalization.ColorfulCaratheodory.Basic
import Formalization.ColorfulCaratheodory.Separation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

open BigOperators Finset

noncomputable section

namespace ColorfulCaratheodory

/-- Predicate stating that `f` is a colorful choice (transversal) from a family of sets `S`. -/
def IsColorfulChoice {d : ℕ} (S : Fin (d + 1) → Set (Fin d → ℝ)) (f : Fin (d + 1) → Fin d → ℝ) : Prop :=
  ∀ i : Fin (d + 1), f i ∈ S i

/-- The colorful simplex (convex hull of the points) formed by a transversal `f`. -/
def colorfulSimplex {d : ℕ} (f : Fin (d + 1) → Fin d → ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range f)

lemma ext_fin1 (x y : Fin 1 → ℝ) (h : x 0 = y 0) : x = y :=
  funext fun i ↦ Subsingleton.elim i 0 ▸ h

lemma exists_le_and_ge_of_mem_convexHull_dim1 {S : Set (Fin 1 → ℝ)} {p : Fin 1 → ℝ}
    (hp : p ∈ convexHull ℝ S) :
    (∃ a ∈ S, a 0 ≤ p 0) ∧ (∃ b ∈ S, p 0 ≤ b 0) := by
  let F := Caratheodory.minCardFinsetOfMemConvexHull hp
  have hF_sub : (F : Set (Fin 1 → ℝ)) ⊆ S := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hp
  have hpF : p ∈ convexHull ℝ (F : Set (Fin 1 → ℝ)) := Caratheodory.mem_minCardFinsetOfMemConvexHull hp
  let v_pos : Fin 1 → ℝ := fun _ ↦ 1
  let v_neg : Fin 1 → ℝ := fun _ ↦ -1
  have h_dot_pos (x : Fin 1 → ℝ) : dotProd v_pos (x - p) = x 0 - p 0 := by
    simp only [dotProd, Fin.sum_univ_one, Pi.sub_apply, v_pos, one_mul]
  have h_dot_neg (x : Fin 1 → ℝ) : dotProd v_neg (x - p) = -(x 0 - p 0) := by
    simp only [dotProd, Fin.sum_univ_one, Pi.sub_apply, v_neg, neg_mul, one_mul]
  obtain ⟨a, haF, h_le_a⟩ := exists_nonpos_dotProd_of_mem_convexHull hpF v_pos
  obtain ⟨b, hbF, h_le_b⟩ := exists_nonpos_dotProd_of_mem_convexHull hpF v_neg
  rw [h_dot_pos] at h_le_a
  rw [h_dot_neg] at h_le_b
  refine ⟨⟨a, hF_sub haF, by linarith⟩, ⟨b, hF_sub hbF, by linarith⟩⟩

lemma mem_convexHull_pair_dim1 (a b p : Fin 1 → ℝ) (h : a 0 ≤ p 0 ∧ p 0 ≤ b 0) :
    p ∈ convexHull ℝ {a, b} := by
  rcases h with ⟨ha, hb⟩
  by_cases heq : a 0 = b 0
  · have : p = a := ext_fin1 p a (by linarith)
    exact this ▸ subset_convexHull ℝ {a, b} (Set.mem_insert a {b})
  · have hlt : a 0 < b 0 := lt_of_le_of_ne (ha.trans hb) heq
    have hdenom : 0 < b 0 - a 0 := sub_pos.mpr hlt
    let c := (b 0 - p 0) / (b 0 - a 0)
    have hc0 : 0 ≤ c := div_nonneg (sub_nonneg.mpr hb) (le_of_lt hdenom)
    have hc1 : c ≤ 1 := (div_le_one hdenom).mpr (by linarith)
    have hcomb : p = c • a + (1 - c) • b := by
      apply ext_fin1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c]
      have hd : b 0 - a 0 ≠ 0 := ne_of_gt hdenom
      have h_cancel : (b 0 - p 0) / (b 0 - a 0) * (b 0 - a 0) = b 0 - p 0 := div_mul_cancel₀ _ hd
      linarith
    rw [hcomb]
    exact convex_convexHull ℝ {a, b}
      (subset_convexHull ℝ _ (Set.mem_insert a {b}))
      (subset_convexHull ℝ _ (Set.mem_insert_of_mem a (Set.mem_singleton b)))
      hc0 (by linarith) (by ring)

/-- **Colorful Carathéodory Theorem in Dimension 1**:
For any two color classes $S_0, S_1 \subset \mathbb{R}^1$ whose convex hulls both contain $p$,
there exists a colorful transversal $f$ ($f(0) \in S_0, f(1) \in S_1$) such that $p \in \operatorname{conv}(\operatorname{range} f)$. -/
theorem colorful_caratheodory_dim1 (S : Fin 2 → Set (Fin 1 → ℝ)) (p : Fin 1 → ℝ)
    (hp : ∀ i : Fin 2, p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 2 → Fin 1 → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := by
  obtain ⟨⟨a, ha, ha_le⟩, -⟩ := exists_le_and_ge_of_mem_convexHull_dim1 (hp 0)
  obtain ⟨-, ⟨b, hb, hb_ge⟩⟩ := exists_le_and_ge_of_mem_convexHull_dim1 (hp 1)
  let f : Fin 2 → Fin 1 → ℝ := fun i ↦ if i = 0 then a else b
  have hf_choice : IsColorfulChoice S f := by
    intro i
    fin_cases i
    · simp [f, ha]
    · simp [f, hb]
  have h_range : Set.range f = {a, b} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, f]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  refine ⟨f, hf_choice, ?_⟩
  dsimp [colorfulSimplex]
  rw [h_range]
  exact mem_convexHull_pair_dim1 a b p ⟨ha_le, hb_ge⟩

end ColorfulCaratheodory
