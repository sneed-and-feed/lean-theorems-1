import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

lemma exists_mem_diff_of_ne {α : Type*} [DecidableEq α] {X s₁ s₂ : Finset α}
    (h₁ : s₁ ⊆ X) (h₂ : s₂ ⊆ X) (hne : s₁ ≠ s₂) :
    ∃ x ∈ X, (x ∈ s₁ ∧ x ∉ s₂) ∨ (x ∈ s₂ ∧ x ∉ s₁) := by
  by_cases h : s₁ ⊆ s₂
  · obtain ⟨x, hx₂, hx₁⟩ := not_subset.mp fun hsub => hne (Subset.antisymm h hsub)
    exact ⟨x, h₂ hx₂, Or.inr ⟨hx₂, hx₁⟩⟩
  · obtain ⟨x, hx₁, hx₂⟩ := not_subset.mp h
    exact ⟨x, h₁ hx₁, Or.inl ⟨hx₁, hx₂⟩⟩

lemma not_mem_of_diff_and_inter_eq {α : Type*} [DecidableEq α] {s₀ s_star S' : Finset α} {x : α}
    (hdiff : (x ∈ s₀ ∧ x ∉ s_star) ∨ (x ∈ s_star ∧ x ∉ s₀))
    (heq : s₀ ∩ S' = s_star ∩ S') : x ∉ S' := by
  intro hxS'
  have := Finset.ext_iff.mp heq x
  simp only [mem_inter] at this
  tauto

lemma inter_subset_inter_of_inter_eq {α : Type*} [DecidableEq α] {s₁ s₂ S S' : Finset α}
    (hS' : S' ⊆ S) (heq : s₁ ∩ S = s₂ ∩ S) : s₁ ∩ S' = s₂ ∩ S' := by
  rw [← inter_eq_right.mpr hS', ← inter_assoc, heq, inter_assoc]

lemma mem_iff_mem_of_inter_insert {α : Type*} [DecidableEq α] {s₁ s₂ S' : Finset α} {x : α}
    (heq : s₁ ∩ (insert x S') = s₂ ∩ (insert x S')) : (x ∈ s₁ ↔ x ∈ s₂) := by
  have := Finset.ext_iff.mp heq x
  simp only [mem_inter, mem_insert] at this
  tauto

lemma diff_mem_iff_false {α : Type*} {x : α} {s₀ s_star : Finset α}
    (hdiff : (x ∈ s₀ ∧ x ∉ s_star) ∨ (x ∈ s_star ∧ x ∉ s₀)) (hiff : x ∈ s₀ ↔ x ∈ s_star) : False := by
  tauto

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
    refine ⟨∅, empty_subset X, by simp [hn1], fun s₁ hs₁ s₂ hs₂ _ => ?_⟩
    rw [hs, mem_singleton] at hs₁ hs₂
    rw [hs₁, hs₂]
  · have hFpos : 0 < F.card := by omega
    obtain ⟨s₀, hs₀⟩ := card_pos.mp hFpos
    let F' := F.erase s₀
    have hF'card : F'.card = n - 1 := by rw [card_erase_of_mem hs₀, hFcard]
    have hF'X : ∀ s ∈ F', s ⊆ X := fun s hs => hFX s (mem_of_mem_erase hs)
    obtain ⟨S', hS'X, hS'card, hS'sep⟩ := ih (n - 1) (by omega) X F' hF'X hF'card (by omega)
    by_cases hex : ∃ s_star ∈ F', s₀ ∩ S' = s_star ∩ S'
    · obtain ⟨s_star, hs_starF', heq_inter⟩ := hex
      have hs₀_ne_s_star : s₀ ≠ s_star := (mem_erase.mp hs_starF').1.symm
      obtain ⟨x, hxX, hdiff⟩ := exists_mem_diff_of_ne (hFX s₀ hs₀) (hFX s_star (mem_of_mem_erase hs_starF')) hs₀_ne_s_star
      have hxS' : x ∉ S' := not_mem_of_diff_and_inter_eq hdiff heq_inter
      refine ⟨insert x S', ?_, ?_, fun s₁ hs₁ s₂ hs₂ heq => ?_⟩
      · intro a ha; rcases mem_insert.mp ha with rfl | ha; exact hxX; exact hS'X ha
      · rw [card_insert_of_notMem hxS']; omega
      · have heqS' : s₁ ∩ S' = s₂ ∩ S' := inter_subset_inter_of_inter_eq (subset_insert x S') heq
        have hx_iff : x ∈ s₁ ↔ x ∈ s₂ := mem_iff_mem_of_inter_insert heq
        by_cases hs₁_eq : s₁ = s₀ <;> by_cases hs₂_eq : s₂ = s₀
        · exact hs₁_eq.trans hs₂_eq.symm
        · have hs₂F' : s₂ ∈ F' := mem_erase.mpr ⟨hs₂_eq, hs₂⟩
          have : s₂ = s_star := hS'sep s₂ hs₂F' s_star hs_starF' (by rw [← heq_inter, ← hs₁_eq, heqS'])
          subst hs₁_eq this
          exact (diff_mem_iff_false hdiff hx_iff).elim
        · have hs₁F' : s₁ ∈ F' := mem_erase.mpr ⟨hs₁_eq, hs₁⟩
          have : s₁ = s_star := hS'sep s₁ hs₁F' s_star hs_starF' (by rw [← heq_inter, ← hs₂_eq, ← heqS'])
          subst hs₂_eq this
          exact (diff_mem_iff_false hdiff hx_iff.symm).elim
        · exact hS'sep s₁ (mem_erase.mpr ⟨hs₁_eq, hs₁⟩) s₂ (mem_erase.mpr ⟨hs₂_eq, hs₂⟩) heqS'
    · refine ⟨S', hS'X, by omega, fun s₁ hs₁ s₂ hs₂ heq => ?_⟩
      by_cases hs₁_eq : s₁ = s₀ <;> by_cases hs₂_eq : s₂ = s₀
      · exact hs₁_eq.trans hs₂_eq.symm
      · exact (hex ⟨s₂, mem_erase.mpr ⟨hs₂_eq, hs₂⟩, by rw [← hs₁_eq, heq]⟩).elim
      · exact (hex ⟨s₁, mem_erase.mpr ⟨hs₁_eq, hs₁⟩, by rw [← hs₂_eq, ← heq]⟩).elim
      · exact hS'sep s₁ (mem_erase.mpr ⟨hs₁_eq, hs₁⟩) s₂ (mem_erase.mpr ⟨hs₂_eq, hs₂⟩) heq

/-- Bondy's Theorem on Induced Subsets (1972):
    Any family F of n distinct subsets of X can be distinguished by a subset S ⊆ X of size ≤ n - 1. -/
theorem bondy_induced_subsets {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α))
    (hFX : ∀ s ∈ F, s ⊆ X)
    (hFn : 1 ≤ F.card) :
    ∃ S ⊆ X, S.card ≤ F.card - 1 ∧
      ∀ s₁ ∈ F, ∀ s₂ ∈ F, s₁ ∩ S = s₂ ∩ S → s₁ = s₂ :=
  bondy_aux F.card X F hFX rfl hFn

/-- Unconditioned Bondy's Theorem on Induced Subsets:
    Any family F of subsets of X can be distinguished by a subset S ⊆ X of size ≤ F.card - 1. -/
theorem bondy_induced_subsets' {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α))
    (hFX : ∀ s ∈ F, s ⊆ X) :
    ∃ S ⊆ X, S.card ≤ F.card - 1 ∧
      ∀ s₁ ∈ F, ∀ s₂ ∈ F, s₁ ∩ S = s₂ ∩ S → s₁ = s₂ := by
  by_cases hFn : 1 ≤ F.card
  · exact bondy_induced_subsets X F hFX hFn
  · have hF0 : F.card = 0 := by omega
    have hF_empty : F = ∅ := Finset.card_eq_zero.mp hF0
    refine ⟨∅, Finset.empty_subset X, by simp [hF0], ?_⟩
    intro s₁ hs₁
    simp [hF_empty] at hs₁

/-- Bondy's theorem formulated as an injection on induced traces:
    There exists S ⊆ X of size ≤ |F| - 1 such that the restriction map s ↦ s ∩ S is injective on F. -/
theorem bondy_induced_injective {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α))
    (hFX : ∀ s ∈ F, s ⊆ X) :
    ∃ S ⊆ X, S.card ≤ F.card - 1 ∧ Set.InjOn (fun s => s ∩ S) (F : Set (Finset α)) := by
  obtain ⟨S, hSX, hScard, hS_inj⟩ := bondy_induced_subsets' X F hFX
  refine ⟨S, hSX, hScard, ?_⟩
  exact fun s₁ hs₁ s₂ hs₂ heq => hS_inj s₁ hs₁ s₂ hs₂ heq
