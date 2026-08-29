import Formalization.ColorfulCaratheodory.Basic
import Formalization.ColorfulCaratheodory.Dim1
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open BigOperators Finset
open Classical

noncomputable section

namespace ColorfulCaratheodory

/-- Point ordering relation on `Fin 1 → ℝ` based on the single coordinate. -/
def pointLE (x y : Fin 1 → ℝ) : Prop := x 0 ≤ y 0

instance : DecidableRel pointLE := fun _ _ ↦ Classical.dec _
instance : IsTrans (Fin 1 → ℝ) pointLE where trans _ _ _ := le_trans
instance : Std.Antisymm pointLE where antisymm _ _ hxy hyx := ext_fin1 _ _ (le_antisymm hxy hyx)
instance : Std.Total pointLE where total _ _ := le_total _ _

lemma get_le_get_of_sorted (P : Finset (Fin 1 → ℝ)) (i j : ℕ)
    (hi : i < (P.sort pointLE).length) (hj : j < (P.sort pointLE).length) (hij : i ≤ j) :
    (P.sort pointLE)[i] 0 ≤ (P.sort pointLE)[j] 0 := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact List.pairwise_iff_get.mp (Finset.pairwise_sort P pointLE) ⟨i, hi⟩ ⟨j, hj⟩ hlt

lemma get_lt_get_of_sorted (P : Finset (Fin 1 → ℝ)) (i j : ℕ)
    (hi : i < (P.sort pointLE).length) (hj : j < (P.sort pointLE).length) (hij : i < j) :
    (P.sort pointLE)[i] 0 < (P.sort pointLE)[j] 0 :=
  lt_of_le_of_ne (get_le_get_of_sorted P i j hi hj hij.le) fun heq ↦ by
    have := (List.Nodup.getElem_inj_iff (Finset.sort_nodup P pointLE)).mp (ext_fin1 _ _ heq)
    omega

/-- **Centerpoint Theorem in Dimension 1**:
For any finite nonempty set $P \subset \mathbb{R}^1$, there exists a centerpoint $p \in \mathbb{R}^1$
(the median) such that every closed half-line containing $p$ contains at least
$\lfloor (|P| + 1) / 2 \rfloor = \lceil |P| / 2 \rceil$ points of $P$. -/
theorem centerpoint_1d (P : Finset (Fin 1 → ℝ)) (hP : P.Nonempty) :
    ∃ p : Fin 1 → ℝ,
      (P.card + 1) / 2 ≤ (P.filter (fun x ↦ x 0 ≤ p 0)).card ∧
      (P.card + 1) / 2 ≤ (P.filter (fun x ↦ p 0 ≤ x 0)).card := by
  let L := P.sort pointLE
  have hL_len : L.length = P.card := Finset.length_sort pointLE
  have hL_nodup : L.Nodup := Finset.sort_nodup P pointLE
  let m := P.card / 2
  have hm : m < L.length := by
    rw [hL_len]
    exact Nat.div_lt_self (Finset.card_pos.mpr hP) (by omega)
  let p := L[m]
  refine ⟨p, ?_, ?_⟩
  · let s1 : Finset (Fin 1 → ℝ) := (Finset.univ : Finset (Fin (m + 1))).image (fun i ↦ L[i.1])
    have hs1_sub : s1 ⊆ P.filter (fun x ↦ x 0 ≤ p 0) := by
      rintro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      have hi_len : i.1 < L.length := by omega
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sort pointLE).mp (List.getElem_mem hi_len),
        get_le_get_of_sorted P i.1 m hi_len hm (by omega)⟩
    have hs1_card : s1.card = m + 1 := by
      rw [Finset.card_image_of_injective _ (fun i j h ↦ Fin.ext ((List.Nodup.getElem_inj_iff hL_nodup).mp h)),
          Finset.card_univ, Fintype.card_fin]
    have h_le := Finset.card_le_card hs1_sub
    omega
  · let s2 : Finset (Fin 1 → ℝ) := (Finset.univ : Finset (Fin (P.card - m))).image (fun i ↦ L[m + i.1])
    have hs2_sub : s2 ⊆ P.filter (fun x ↦ p 0 ≤ x 0) := by
      rintro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      have hi_len : m + i.1 < L.length := by omega
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sort pointLE).mp (List.getElem_mem hi_len),
        get_le_get_of_sorted P m (m + i.1) hm hi_len (by omega)⟩
    have hs2_card : s2.card = P.card - m := by
      rw [Finset.card_image_of_injective _ (fun i j h ↦ Fin.ext (by have := (List.Nodup.getElem_inj_iff hL_nodup).mp h; omega)),
          Finset.card_univ, Fintype.card_fin]
    have h_le := Finset.card_le_card hs2_sub
    omega

/-- **Bárány's First Selection Lemma in Dimension 1**:
For any finite set $P \subset \mathbb{R}^1$ with $|P| \ge 2$, there exists a point $p \in \mathbb{R}^1$
(the median) with halfspace depth at least $\lfloor (|P| + 1) / 2 \rfloor = \lceil |P| / 2 \rceil$
and contained in at least $(|P| / 2) \cdot (|P| - |P| / 2)$ pairs $\{a, b\} \subseteq P$ whose convex hull contains $p$. -/
theorem first_selection_lemma_1d (P : Finset (Fin 1 → ℝ)) (hP : 2 ≤ P.card) :
    ∃ p : Fin 1 → ℝ,
      (P.card + 1) / 2 ≤ (P.filter (fun x ↦ x 0 ≤ p 0)).card ∧
      (P.card + 1) / 2 ≤ (P.filter (fun x ↦ p 0 ≤ x 0)).card ∧
      (P.card / 2) * (P.card - P.card / 2) ≤
        ((P.powersetCard 2).filter (fun (s : Finset (Fin 1 → ℝ)) ↦ p ∈ convexHull ℝ (s : Set (Fin 1 → ℝ)))).card := by
  let L := P.sort pointLE
  have hL_len : L.length = P.card := Finset.length_sort pointLE
  have hL_nodup : L.Nodup := Finset.sort_nodup P pointLE
  let m := P.card / 2
  have hm_len : m < L.length := by rw [hL_len]; exact Nat.div_lt_self (by omega) (by omega)
  let p := L[m]
  have hs1_le : (P.card + 1) / 2 ≤ (P.filter (fun x ↦ x 0 ≤ p 0)).card := by
    let s1 : Finset (Fin 1 → ℝ) := (Finset.univ : Finset (Fin (m + 1))).image (fun i ↦ L[i.1])
    have hs1_sub : s1 ⊆ P.filter (fun x ↦ x 0 ≤ p 0) := by
      rintro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      have hi_len : i.1 < L.length := by omega
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sort pointLE).mp (List.getElem_mem hi_len),
        get_le_get_of_sorted P i.1 m hi_len hm_len (by omega)⟩
    have hs1_card : s1.card = m + 1 := by
      rw [Finset.card_image_of_injective _ (fun i j h ↦ Fin.ext ((List.Nodup.getElem_inj_iff hL_nodup).mp h)),
          Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_card hs1_sub
    omega
  have hs2_le : (P.card + 1) / 2 ≤ (P.filter (fun x ↦ p 0 ≤ x 0)).card := by
    let s2 : Finset (Fin 1 → ℝ) := (Finset.univ : Finset (Fin (P.card - m))).image (fun i ↦ L[m + i.1])
    have hs2_sub : s2 ⊆ P.filter (fun x ↦ p 0 ≤ x 0) := by
      rintro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      have hi_len : m + i.1 < L.length := by omega
      exact Finset.mem_filter.mpr ⟨(Finset.mem_sort pointLE).mp (List.getElem_mem hi_len),
        get_le_get_of_sorted P m (m + i.1) hm_len hi_len (by omega)⟩
    have hs2_card : s2.card = P.card - m := by
      rw [Finset.card_image_of_injective _ (fun i j h ↦ Fin.ext (by have := (List.Nodup.getElem_inj_iff hL_nodup).mp h; omega)),
          Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_card hs2_sub
    omega
  let g (ij : Fin m × Fin (P.card - m)) : Finset (Fin 1 → ℝ) := {L[ij.1.1], L[m + ij.2.1]}
  have hg_sub : (Finset.univ : Finset (Fin m × Fin (P.card - m))).image g ⊆
      (P.powersetCard 2).filter (fun (s : Finset (Fin 1 → ℝ)) ↦ p ∈ convexHull ℝ (s : Set (Fin 1 → ℝ))) := by
    rintro s hs
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hs
    have hi_len : i.1 < L.length := by omega
    have hj_len : m + j.1 < L.length := by omega
    have h_lt : L[i.1] 0 < L[m + j.1] 0 := get_lt_get_of_sorted P i.1 (m + j.1) hi_len hj_len (by omega)
    have hs_card : ({L[i.1], L[m + j.1]} : Finset (Fin 1 → ℝ)).card = 2 :=
      Finset.card_pair (fun h ↦ ne_of_lt h_lt (congrArg (fun x ↦ x 0) h))
    have hs_subset : ({L[i.1], L[m + j.1]} : Finset (Fin 1 → ℝ)) ⊆ P := by
      rintro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact (Finset.mem_sort pointLE).mp (List.getElem_mem (by omega))
    have hs_power := Finset.mem_powersetCard.mpr ⟨hs_subset, hs_card⟩
    have hp_mem : p ∈ convexHull ℝ ({L[i.1], L[m + j.1]} : Set (Fin 1 → ℝ)) :=
      mem_convexHull_pair_dim1 L[i.1] L[m + j.1] p
        ⟨get_le_get_of_sorted P i.1 m hi_len hm_len (by omega),
         get_le_get_of_sorted P m (m + j.1) hm_len hj_len (by omega)⟩
    exact Finset.mem_filter.mpr ⟨hs_power, by rwa [Finset.coe_pair]⟩
  have hg_inj : ∀ ij1 ij2 : Fin m × Fin (P.card - m), g ij1 = g ij2 → ij1 = ij2 := by
    rintro ⟨i1, j1⟩ ⟨i2, j2⟩ hg_eq
    have hi1_len : i1.1 < L.length := by omega
    have hj1_len : m + j1.1 < L.length := by omega
    have hi2_len : i2.1 < L.length := by omega
    have hj2_len : m + j2.1 < L.length := by omega
    have h_lt1 : L[i1.1] 0 < L[m + j1.1] 0 := get_lt_get_of_sorted P i1.1 (m + j1.1) hi1_len hj1_len (by omega)
    have h_lt2 : L[i2.1] 0 < L[m + j2.1] 0 := get_lt_get_of_sorted P i2.1 (m + j2.1) hi2_len hj2_len (by omega)
    have hi1_mem : L[i1.1] ∈ g (i2, j2) := by rw [← hg_eq]; simp [g]
    have hj1_mem : L[m + j1.1] ∈ g (i2, j2) := by rw [← hg_eq]; simp [g]
    dsimp [g] at hi1_mem hj1_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi1_mem hj1_mem
    rcases hi1_mem with heq_i1 | heq_i2 <;> rcases hj1_mem with heq_j1 | heq_j2
    · have heq : L[i1.1] 0 = L[m + j1.1] 0 := (congrArg (fun x ↦ x 0) heq_i1).trans (congrArg (fun x ↦ x 0) heq_j1).symm
      linarith
    · have heq1 := (List.Nodup.getElem_inj_iff hL_nodup).mp heq_i1
      have heq2 := (List.Nodup.getElem_inj_iff hL_nodup).mp heq_j2
      have hj_eq : j1.1 = j2.1 := by omega
      exact Prod.ext (Fin.ext heq1) (Fin.ext hj_eq)
    · exfalso
      have heq_i0 : L[i1.1] 0 = L[m + j2.1] 0 := congrArg (fun x ↦ x 0) heq_i2
      have heq_j0 : L[m + j1.1] 0 = L[i2.1] 0 := congrArg (fun x ↦ x 0) heq_j1
      linarith
    · have heq : L[i1.1] 0 = L[m + j1.1] 0 := (congrArg (fun x ↦ x 0) heq_i2).trans (congrArg (fun x ↦ x 0) heq_j2).symm
      linarith
  have h_le := Finset.card_le_card hg_sub
  rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h_le
  refine ⟨p, hs1_le, hs2_le, h_le⟩

/-- Combinatorial cross-product lower bound for colorful selection in dimension 1. -/
theorem colorful_selection_lemma_1d_product (S : Fin 2 → Finset (Fin 1 → ℝ)) (p : Fin 1 → ℝ) :
    ((S 0).filter (fun x ↦ x 0 ≤ p 0)).card * ((S 1).filter (fun x ↦ p 0 ≤ x 0)).card ≤
      ((S 0 ×ˢ S 1).filter (fun (ab : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ↦
        p ∈ convexHull ℝ ({ab.1, ab.2} : Set (Fin 1 → ℝ)))).card := by
  let A := (S 0).filter (fun x ↦ x 0 ≤ p 0)
  let B := (S 1).filter (fun x ↦ p 0 ≤ x 0)
  have h_sub : A ×ˢ B ⊆ (S 0 ×ˢ S 1).filter (fun ab ↦ p ∈ convexHull ℝ ({ab.1, ab.2} : Set (Fin 1 → ℝ))) := by
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hab.1.1, hab.2.1⟩,
      mem_convexHull_pair_dim1 a b p ⟨hab.1.2, hab.2.2⟩⟩
  rw [← Finset.card_product]
  exact Finset.card_le_card h_sub

/-- **Colorful Selection Lemma in Dimension 1**:
For any two finite color classes $S_0, S_1 \subset \mathbb{R}^1$ whose convex hulls both contain a point $p$,
there exists at least one colorful pair $(a, b) \in S_0 \times S_1$ whose convex hull contains $p$. -/
theorem colorful_selection_lemma_1d (S : Fin 2 → Finset (Fin 1 → ℝ)) (p : Fin 1 → ℝ)
    (hp : ∀ i : Fin 2, p ∈ convexHull ℝ (S i : Set (Fin 1 → ℝ))) :
    1 ≤ ((S 0 ×ˢ S 1).filter (fun (ab : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ↦
      p ∈ convexHull ℝ ({ab.1, ab.2} : Set (Fin 1 → ℝ)))).card := by
  obtain ⟨⟨a, ha_mem, ha_le⟩, -⟩ := exists_le_and_ge_of_mem_convexHull_dim1 (hp 0)
  obtain ⟨-, ⟨b, hb_mem, hb_ge⟩⟩ := exists_le_and_ge_of_mem_convexHull_dim1 (hp 1)
  have hA_pos : 0 < ((S 0).filter (fun x ↦ x 0 ≤ p 0)).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha_mem, ha_le⟩⟩
  have hB_pos : 0 < ((S 1).filter (fun x ↦ p 0 ≤ x 0)).card :=
    Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hb_mem, hb_ge⟩⟩
  have h_pos : 1 ≤ ((S 0).filter (fun x ↦ x 0 ≤ p 0)).card * ((S 1).filter (fun x ↦ p 0 ≤ x 0)).card := by
    nlinarith
  exact h_pos.trans (colorful_selection_lemma_1d_product S p)

end ColorfulCaratheodory