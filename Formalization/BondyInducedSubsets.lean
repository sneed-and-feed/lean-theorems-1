import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

lemma exists_mem_diff_of_ne {α : Type*} [DecidableEq α] {X s₁ s₂ : Finset α}
    (h₁ : s₁ ⊆ X) (h₂ : s₂ ⊆ X) (hne : s₁ ≠ s₂) :
    ∃ x ∈ X, (x ∈ s₁ ∧ x ∉ s₂) ∨ (x ∈ s₂ ∧ x ∉ s₁) := by
  by_cases h : s₁ ⊆ s₂
  · have hnot : ¬ s₂ ⊆ s₁ := fun hsub => hne (Finset.Subset.antisymm h hsub)
    obtain ⟨x, hx₂, hx₁⟩ := Finset.not_subset.mp hnot
    exact ⟨x, h₂ hx₂, Or.inr ⟨hx₂, hx₁⟩⟩
  · obtain ⟨x, hx₁, hx₂⟩ := Finset.not_subset.mp h
    exact ⟨x, h₁ hx₁, Or.inl ⟨hx₁, hx₂⟩⟩

lemma not_mem_of_diff_and_inter_eq {α : Type*} [DecidableEq α] {s₀ s_star S' : Finset α} {x : α}
    (hdiff : (x ∈ s₀ ∧ x ∉ s_star) ∨ (x ∈ s_star ∧ x ∉ s₀))
    (heq : s₀ ∩ S' = s_star ∩ S') :
    x ∉ S' := by
  intro hxS'
  have hmem : x ∈ s₀ ∩ S' ↔ x ∈ s_star ∩ S' := by rw [heq]
  simp only [Finset.mem_inter, hxS', and_true] at hmem
  rcases hdiff with ⟨hx₀, hxs⟩ | ⟨hxs, hx₀⟩
  · exact hxs (hmem.mp hx₀)
  · exact hx₀ (hmem.mpr hxs)

lemma inter_subset_inter_of_inter_eq {α : Type*} [DecidableEq α] {s₁ s₂ S S' : Finset α}
    (hS' : S' ⊆ S) (heq : s₁ ∩ S = s₂ ∩ S) : s₁ ∩ S' = s₂ ∩ S' := by
  have h (s : Finset α) : s ∩ S' = (s ∩ S) ∩ S' := by
    ext a
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨ha_s, ha_S'⟩
      exact ⟨⟨ha_s, hS' ha_S'⟩, ha_S'⟩
    · rintro ⟨⟨ha_s, _⟩, ha_S'⟩
      exact ⟨ha_s, ha_S'⟩
  rw [h s₁, heq, ← h s₂]

lemma mem_iff_mem_of_inter_insert {α : Type*} [DecidableEq α] {s₁ s₂ S' : Finset α} {x : α}
    (heq : s₁ ∩ (insert x S') = s₂ ∩ (insert x S')) :
    (x ∈ s₁ ↔ x ∈ s₂) := by
  have h₁ : x ∈ s₁ ∩ insert x S' ↔ x ∈ s₁ := by
    simp only [Finset.mem_inter, Finset.mem_insert_self, and_true]
  have h₂ : x ∈ s₂ ∩ insert x S' ↔ x ∈ s₂ := by
    simp only [Finset.mem_inter, Finset.mem_insert_self, and_true]
  rw [← h₁, heq, h₂]

lemma diff_mem_iff_false {α : Type*} {x : α} {s₀ s_star : Finset α}
    (hdiff : (x ∈ s₀ ∧ x ∉ s_star) ∨ (x ∈ s_star ∧ x ∉ s₀)) (hiff : x ∈ s₀ ↔ x ∈ s_star) : False := by
  rcases hdiff with ⟨hx₀, hxs⟩ | ⟨hxs, hx₀⟩
  · exact hxs (hiff.mp hx₀)
  · exact hx₀ (hiff.mpr hxs)

lemma bondy_aux (n : ℕ) :
    ∀ {α : Type*} [DecidableEq α] (X : Finset α) (F : Finset (Finset α)),
      (∀ s ∈ F, s ⊆ X) → F.card = n → 1 ≤ n →
      ∃ S ⊆ X, S.card ≤ n - 1 ∧
        ∀ s₁ ∈ F, ∀ s₂ ∈ F, s₁ ∩ S = s₂ ∩ S → s₁ = s₂ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro α _ X F hFX hFcard hn
  by_cases hn1 : n = 1
  · obtain ⟨s, hs⟩ := Finset.card_eq_one.mp (hFcard.trans hn1)
    refine ⟨∅, Finset.empty_subset X, by simp [hn1], fun s₁ hs₁ s₂ hs₂ _ => ?_⟩
    rw [hs, Finset.mem_singleton] at hs₁ hs₂
    rw [hs₁, hs₂]
  · have hn2 : 2 ≤ n := by omega
    have hFpos : 0 < F.card := by omega
    obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp hFpos
    let F' := F.erase s₀
    have hF'card : F'.card = n - 1 := by
      rw [Finset.card_erase_of_mem hs₀, hFcard]
    have hF'X : ∀ s ∈ F', s ⊆ X := by
      intro s hs
      exact hFX s (Finset.mem_of_mem_erase hs)
    have h1le : 1 ≤ n - 1 := by omega
    have hlt : n - 1 < n := by omega
    obtain ⟨S', hS'X, hS'card, hS'sep⟩ := ih (n - 1) hlt X F' hF'X hF'card h1le
    by_cases hex : ∃ s_star ∈ F', s₀ ∩ S' = s_star ∩ S'
    · obtain ⟨s_star, hs_starF', heq_inter⟩ := hex
      have hs₀_ne_s_star : s₀ ≠ s_star := (Finset.mem_erase.mp hs_starF').1.symm
      have hs₀X : s₀ ⊆ X := hFX s₀ hs₀
      have hs_starX : s_star ⊆ X := hFX s_star (Finset.mem_of_mem_erase hs_starF')
      obtain ⟨x, hxX, hdiff⟩ := exists_mem_diff_of_ne hs₀X hs_starX hs₀_ne_s_star
      have hxS' : x ∉ S' := not_mem_of_diff_and_inter_eq hdiff heq_inter
      have hSX : insert x S' ⊆ X := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hxX
        · exact hS'X ha
      have hScard : (insert x S').card ≤ n - 1 := by
        rw [Finset.card_insert_of_notMem hxS']
        omega
      refine ⟨insert x S', hSX, hScard, fun s₁ hs₁ s₂ hs₂ heq => ?_⟩
      have hS'subS : S' ⊆ insert x S' := Finset.subset_insert x S'
      have heqS' : s₁ ∩ S' = s₂ ∩ S' := inter_subset_inter_of_inter_eq hS'subS heq
      have hx_iff : (x ∈ s₁ ↔ x ∈ s₂) := mem_iff_mem_of_inter_insert heq
      by_cases hs₁_eq : s₁ = s₀
      · by_cases hs₂_eq : s₂ = s₀
        · exact hs₁_eq.trans hs₂_eq.symm
        · have hs₂F' : s₂ ∈ F' := Finset.mem_erase.mpr ⟨hs₂_eq, hs₂⟩
          have heq_s₂_s_star : s₂ ∩ S' = s_star ∩ S' := by
            rw [← heq_inter, ← hs₁_eq, heqS']
          have hs₂_eq_s_star : s₂ = s_star := hS'sep s₂ hs₂F' s_star hs_starF' heq_s₂_s_star
          have hx_iff' : x ∈ s₀ ↔ x ∈ s_star := by
            rw [← hs₁_eq, ← hs₂_eq_s_star]
            exact hx_iff
          exfalso
          exact diff_mem_iff_false hdiff hx_iff'
      · have hs₁F' : s₁ ∈ F' := Finset.mem_erase.mpr ⟨hs₁_eq, hs₁⟩
        by_cases hs₂_eq : s₂ = s₀
        · have heq_s₁_s_star : s₁ ∩ S' = s_star ∩ S' := by
            rw [← heq_inter, ← hs₂_eq, ← heqS']
          have hs₁_eq_s_star : s₁ = s_star := hS'sep s₁ hs₁F' s_star hs_starF' heq_s₁_s_star
          have hx_iff' : x ∈ s₀ ↔ x ∈ s_star := by
            rw [← hs₂_eq, ← hs₁_eq_s_star]
            exact hx_iff.symm
          exfalso
          exact diff_mem_iff_false hdiff hx_iff'
        · have hs₂F' : s₂ ∈ F' := Finset.mem_erase.mpr ⟨hs₂_eq, hs₂⟩
          exact hS'sep s₁ hs₁F' s₂ hs₂F' heqS'
    · refine ⟨S', hS'X, by omega, fun s₁ hs₁ s₂ hs₂ heq => ?_⟩
      by_cases hs₁_eq : s₁ = s₀
      · by_cases hs₂_eq : s₂ = s₀
        · exact hs₁_eq.trans hs₂_eq.symm
        · have hs₂F' : s₂ ∈ F' := Finset.mem_erase.mpr ⟨hs₂_eq, hs₂⟩
          have heq' : s₀ ∩ S' = s₂ ∩ S' := by rw [← hs₁_eq, heq]
          exfalso
          exact hex ⟨s₂, hs₂F', heq'⟩
      · have hs₁F' : s₁ ∈ F' := Finset.mem_erase.mpr ⟨hs₁_eq, hs₁⟩
        by_cases hs₂_eq : s₂ = s₀
        · have heq' : s₀ ∩ S' = s₁ ∩ S' := by rw [← hs₂_eq, ← heq]
          exfalso
          exact hex ⟨s₁, hs₁F', heq'⟩
        · have hs₂F' : s₂ ∈ F' := Finset.mem_erase.mpr ⟨hs₂_eq, hs₂⟩
          exact hS'sep s₁ hs₁F' s₂ hs₂F' heq

/-- Bondy's Theorem on Induced Subsets (1972):
    Any family F of n distinct subsets of X can be distinguished by a subset S ⊆ X of size ≤ n - 1. -/
theorem bondy_induced_subsets {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α))
    (hFX : ∀ s ∈ F, s ⊆ X)
    (hFn : 1 ≤ F.card) :
    ∃ S ⊆ X, S.card ≤ F.card - 1 ∧
      ∀ s₁ ∈ F, ∀ s₂ ∈ F, s₁ ∩ S = s₂ ∩ S → s₁ = s₂ :=
  bondy_aux F.card X F hFX rfl hFn

