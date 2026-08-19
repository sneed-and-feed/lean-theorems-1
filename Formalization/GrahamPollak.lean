import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset

/-- A complete bipartite decomposition of K_n is given by a family of pairs of disjoint subsets
    (L_k, R_k) such that every distinct pair of vertices {u, v} is covered by exactly one bipartite graph. -/
def IsCompleteBipartitePartition (n m : ℕ) (L R : Fin m → Finset (Fin n)) : Prop :=
  (∀ k, Disjoint (L k) (R k)) ∧
  (∀ u v : Fin n, u ≠ v →
    ∃! k : Fin m, (u ∈ L k ∧ v ∈ R k) ∨ (u ∈ R k ∧ v ∈ L k))

lemma sum_sq_identity (n : ℕ) (x : Fin n → ℝ) :
    (∑ i : Fin n, x i) ^ 2 = ∑ i : Fin n, (x i) ^ 2 + 2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0 := by
  have h_sq : (∑ i : Fin n, x i) ^ 2 = (∑ i : Fin n, x i) * (∑ j : Fin n, x j) := sq (∑ i, x i)
  rw [h_sq, Fintype.sum_mul_sum]
  have h_split : (∑ i : Fin n, ∑ j : Fin n, x i * x j) =
      (∑ i : Fin n, ∑ j : Fin n, ((if i = j then x i * x j else 0) +
        (if i < j then x i * x j else 0) + (if j < i then x i * x j else 0))) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with hij | rfl | hji
    · have h1 : ¬ (i = j) := ne_of_lt hij
      have h2 : ¬ (j < i) := not_lt_of_gt hij
      simp [hij, h1, h2]
    · simp
    · have h1 : ¬ (i = j) := ne_of_gt hji
      have h2 : ¬ (i < j) := not_lt_of_gt hji
      simp [hji, h1, h2]
  rw [h_split]
  simp only [sum_add_distrib]
  have h_diag : (∑ i : Fin n, ∑ j : Fin n, if i = j then x i * x j else 0) = ∑ i : Fin n, (x i) ^ 2 := by
    apply Finset.sum_congr rfl; intro i _
    simp [sq]
  have h_symm : (∑ i : Fin n, ∑ j : Fin n, if j < i then x i * x j else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mul_comm]
  rw [h_diag, h_symm]
  ring

lemma sum_finset_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) = ∑ i : α, if i ∈ s then f i else 0 := by
  have h : s = univ.filter (· ∈ s) := by
    ext a
    simp
  nth_rw 1 [h]
  rw [sum_filter]

lemma ite_mul_ite_zero (P Q : Prop) [Decidable P] [Decidable Q] (a b : ℝ) :
    ((if P then a else 0) * (if Q then b else 0)) = if P ∧ Q then a * b else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma sum_pair_indicator {m : ℕ} (P Q : Fin m → Prop) [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ k, ¬ (P k ∧ Q k))
    (h_uniq : ∃! k, P k ∨ Q k)
    (C : ℝ) :
    (∑ k : Fin m, ((if P k then C else 0) + (if Q k then C else 0))) = C := by
  rcases h_uniq with ⟨k0, hk0_or, hk0_uniq⟩
  have h_k0 : (if P k0 then C else 0) + (if Q k0 then C else 0) = C := by
    rcases hk0_or with hP | hQ
    · have hnotQ : ¬ Q k0 := fun h => h_disj k0 ⟨hP, h⟩
      simp [hP, hnotQ]
    · have hnotP : ¬ P k0 := fun h => h_disj k0 ⟨h, hQ⟩
      simp [hQ, hnotP]
  have h_others : ∀ k : Fin m, k ≠ k0 → (if P k then C else 0) + (if Q k then C else 0) = 0 := by
    intro k hk
    have hnotP : ¬ P k := fun h => hk (hk0_uniq k (Or.inl h))
    have hnotQ : ¬ Q k := fun h => hk (hk0_uniq k (Or.inr h))
    simp [hnotP, hnotQ]
  rw [Finset.sum_eq_single k0]
  · exact h_k0
  · intro k _ hk
    exact h_others k hk
  · intro h_not_mem
    exact False.elim (h_not_mem (Finset.mem_univ k0))

/-- Sub-lemma 2: Bipartite edge sum equals product sum. -/
lemma bipartite_sum_eq (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) =
      ∑ k : Fin m, (∑ i ∈ L k, x i) * (∑ j ∈ R k, x j) := by
  have h_rhs_expand : (∑ k : Fin m, (∑ i ∈ L k, x i) * (∑ j ∈ R k, x j)) =
      ∑ k : Fin m, ∑ i : Fin n, ∑ j : Fin n, if i ∈ L k ∧ j ∈ R k then x i * x j else 0 := by
    apply Finset.sum_congr rfl; intro k _
    rw [sum_finset_eq_sum_ite (L k) x, sum_finset_eq_sum_ite (R k) x, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [ite_mul_ite_zero]
  rw [h_rhs_expand]
  have h_interchange : (∑ k : Fin m, ∑ i : Fin n, ∑ j : Fin n, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
  rw [h_interchange]
  have h_split : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) =
      (∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) +
         (if i < j then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) +
         (if j < i then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0))) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with hij | rfl | hji
    · have h1 : ¬ (i = j) := ne_of_lt hij
      have h2 : ¬ (j < i) := not_lt_of_gt hij
      simp [hij, h1, h2]
    · simp
    · have h1 : ¬ (i = j) := ne_of_gt hji
      have h2 : ¬ (i < j) := not_lt_of_gt hji
      simp [hji, h1, h2]
  rw [h_split]
  simp only [sum_add_distrib]
  have h_diag : (∑ i : Fin n, ∑ j : Fin n, if i = j then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      apply Finset.sum_eq_zero; intro k _
      have h_disj : ¬ (i ∈ L k ∧ i ∈ R k) := fun ⟨hiL, hiR⟩ =>
        Finset.disjoint_left.mp (h.1 k) hiL hiR
      simp [h_disj]
    · intro j _ hne
      have hne' : ¬ (i = j) := fun heq => hne heq.symm
      simp [hne']
    · intro h_not
      exact False.elim (h_not (Finset.mem_univ i))
  have h_symm : (∑ i : Fin n, ∑ j : Fin n, if j < i then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then (∑ k : Fin m, if j ∈ L k ∧ i ∈ R k then x i * x j else 0) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    split_ifs with hij
    · apply Finset.sum_congr rfl; intro k _
      rw [mul_comm]
    · rfl
  rw [h_diag, zero_add, h_symm, ← sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  split_ifs with hij
  · rw [← Finset.sum_add_distrib]
    have h_disj : ∀ k, ¬ ((i ∈ L k ∧ j ∈ R k) ∧ (j ∈ L k ∧ i ∈ R k)) := by
      intro k ⟨⟨hiL, _⟩, ⟨_, hiR⟩⟩
      exact Finset.disjoint_left.mp (h.1 k) hiL hiR
    have h_uniq : ∃! k, (i ∈ L k ∧ j ∈ R k) ∨ (j ∈ L k ∧ i ∈ R k) := by
      have h_orig := h.2 i j (ne_of_lt hij)
      rcases h_orig with ⟨k0, hk0_or, hk0_uniq⟩
      refine ⟨k0, ?_, ?_⟩
      · rcases hk0_or with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨h2.2, h2.1⟩
      · intro k hk_or
        apply hk0_uniq
        rcases hk_or with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨h2.2, h2.1⟩
    exact (sum_pair_indicator (fun k => i ∈ L k ∧ j ∈ R k) (fun k => j ∈ L k ∧ i ∈ R k) h_disj h_uniq (x i * x j)).symm
  · simp

/-- Linear map associated with Graham-Pollak bipartite decomposition. -/
def gpLinearMap (n m : ℕ) (L : Fin m → Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (ℝ × (Fin m → ℝ)) where
  toFun x := (∑ i, x i, fun k => ∑ i ∈ L k, x i)
  map_add' x y := by
    ext
    · simp only [Pi.add_apply, sum_add_distrib, Prod.fst_add]
    · simp only [Pi.add_apply, sum_add_distrib, Prod.snd_add]
  map_smul' c x := by
    ext
    · simp only [Pi.smul_apply, smul_eq_mul, mul_sum, RingHom.id_apply, Prod.smul_fst]
    · simp only [Pi.smul_apply, smul_eq_mul, mul_sum, RingHom.id_apply, Prod.smul_snd]

lemma gpLinearMap_injective (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) :
    Function.Injective (gpLinearMap n m L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h_sum_zero : ∑ i : Fin n, x i = 0 := by
    have h1 : (gpLinearMap n m L x).1 = (0 : ℝ × (Fin m → ℝ)).1 := by rw [hx]
    exact h1
  have h_L_zero : ∀ k : Fin m, ∑ i ∈ L k, x i = 0 := by
    intro k
    have h2 : (gpLinearMap n m L x).2 = (0 : ℝ × (Fin m → ℝ)).2 := by rw [hx]
    exact congr_fun h2 k
  have h_prod_zero : ∑ k : Fin m, (∑ i ∈ L k, x i) * (∑ j ∈ R k, x j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [h_L_zero k, zero_mul]
  have h_cross : (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) = 0 := by
    rw [bipartite_sum_eq n m L R h x, h_prod_zero]
  have h_sq_id := sum_sq_identity n x
  rw [h_sum_zero, h_cross, mul_zero, add_zero, sq, mul_zero] at h_sq_id
  have h_sum_sq : ∑ i : Fin n, (x i) ^ 2 = 0 := h_sq_id.symm
  have h_nonneg : ∀ i ∈ (univ : Finset (Fin n)), 0 ≤ (x i) ^ 2 := fun i _ => sq_nonneg (x i)
  rw [Finset.sum_eq_zero_iff_of_nonneg h_nonneg] at h_sum_sq
  ext i
  have h_xi_sq : (x i) ^ 2 = 0 := h_sum_sq i (Finset.mem_univ i)
  have h_xi : x i = 0 := sq_eq_zero_iff.mp h_xi_sq
  exact h_xi


/-- Main Theorem: Graham-Pollak Theorem (1971 / Tverberg 1982). -/
theorem graham_pollak (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) :
    n - 1 ≤ m := by
  have hinj := gpLinearMap_injective n m L R h
  have h_rank := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_self] at h_rank
  omega
