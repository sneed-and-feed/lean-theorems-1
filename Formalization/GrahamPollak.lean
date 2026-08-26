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
  rw [sq, Fintype.sum_mul_sum]
  have : (∑ i : Fin n, ∑ j : Fin n, x i * x j) = ∑ i : Fin n, ∑ j : Fin n, ((if i = j then x i * x j else 0) + (if i < j then x i * x j else 0) + (if j < i then x i * x j else 0)) := by
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _
    rcases lt_trichotomy i j with hij | rfl | hji
    · have h1 : i ≠ j := ne_of_lt hij; have h2 : ¬(j < i) := not_lt_of_gt hij; simp [hij, h1, h2]
    · simp
    · have h1 : i ≠ j := ne_of_gt hji; have h2 : ¬(i < j) := not_lt_of_gt hji; simp [hji, h1, h2]
  rw [this]
  simp_rw [sum_add_distrib]
  have h_diag : (∑ i : Fin n, ∑ j : Fin n, if i = j then x i * x j else 0) = ∑ i : Fin n, (x i) ^ 2 := by
    apply sum_congr rfl; intro i _; simp [sq]
  have h_symm : (∑ i : Fin n, ∑ j : Fin n, if j < i then x i * x j else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) := by
    rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_comm]
  rw [h_diag, h_symm]
  ring

lemma sum_finset_eq_sum_ite {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) = ∑ i : α, if i ∈ s then f i else 0 := by
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]

lemma ite_mul_ite_zero (P Q : Prop) [Decidable P] [Decidable Q] (a b : ℝ) :
    ((if P then a else 0) * (if Q then b else 0)) = if P ∧ Q then a * b else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma sum_pair_indicator {m : ℕ} (P Q : Fin m → Prop) [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ k, ¬ (P k ∧ Q k))
    (h_uniq : ∃! k, P k ∨ Q k)
    (C : ℝ) :
    (∑ k : Fin m, ((if P k then C else 0) + (if Q k then C else 0))) = C := by
  rcases h_uniq with ⟨k0, hk0_or, hk0_uniq⟩
  rw [Finset.sum_eq_single k0]
  · rcases hk0_or with hP | hQ
    · have hQ0 : ¬ Q k0 := fun h => h_disj k0 ⟨hP, h⟩; simp [hP, hQ0]
    · have hP0 : ¬ P k0 := fun h => h_disj k0 ⟨h, hQ⟩; simp [hQ, hP0]
  · intro k _ hk
    have hPk : ¬ P k := fun h => hk (hk0_uniq k (Or.inl h))
    have hQk : ¬ Q k := fun h => hk (hk0_uniq k (Or.inr h))
    simp [hPk, hQk]
  · simp

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
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]
  rw [h_interchange]
  have h_split : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) =
      (∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) +
         (if i < j then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) +
         (if j < i then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0))) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with hij | rfl | hji
    · have h1 : i ≠ j := ne_of_lt hij; have h2 : ¬ (j < i) := not_lt_of_gt hij; simp [hij, h1, h2]
    · simp
    · have h1 : i ≠ j := ne_of_gt hji; have h2 : ¬ (i < j) := not_lt_of_gt hji; simp [hji, h1, h2]
  rw [h_split]
  simp_rw [sum_add_distrib]
  have h_diag : (∑ i : Fin n, ∑ j : Fin n, if i = j then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) = 0 := by
    apply Finset.sum_eq_zero; intro i _; rw [Finset.sum_eq_single i]
    · simp only [ite_true]; apply Finset.sum_eq_zero; intro k _
      have h_disj : ¬ (i ∈ L k ∧ i ∈ R k) := fun ⟨hiL, hiR⟩ => Finset.disjoint_left.mp (h.1 k) hiL hiR
      simp [h_disj]
    · intro j _ hne; have hne' : i ≠ j := fun heq => hne heq.symm; simp [hne']
    · intro h_not; exact False.elim (h_not (Finset.mem_univ i))
  have h_symm : (∑ i : Fin n, ∑ j : Fin n, if j < i then (∑ k : Fin m, if i ∈ L k ∧ j ∈ R k then x i * x j else 0) else 0) =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then (∑ k : Fin m, if j ∈ L k ∧ i ∈ R k then x i * x j else 0) else 0) := by
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    split_ifs with hij
    · apply Finset.sum_congr rfl; intro k _; rw [mul_comm]
    · rfl
  rw [h_diag, zero_add, h_symm]
  simp_rw [← sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  split_ifs with hij
  · rw [← Finset.sum_add_distrib]
    have h_disj : ∀ k, ¬ ((i ∈ L k ∧ j ∈ R k) ∧ (j ∈ L k ∧ i ∈ R k)) := by
      intro k ⟨⟨hiL, _⟩, ⟨_, hiR⟩⟩; exact Finset.disjoint_left.mp (h.1 k) hiL hiR
    have h_uniq : ∃! k, (i ∈ L k ∧ j ∈ R k) ∨ (j ∈ L k ∧ i ∈ R k) := by
      rcases h.2 i j (ne_of_lt hij) with ⟨k0, hk0_or, hk0_uniq⟩
      refine ⟨k0, hk0_or.casesOn Or.inl (fun h2 => Or.inr ⟨h2.2, h2.1⟩), fun k hk_or => hk0_uniq k (hk_or.casesOn Or.inl (fun h2 => Or.inr ⟨h2.2, h2.1⟩))⟩
    exact (sum_pair_indicator (fun k => i ∈ L k ∧ j ∈ R k) (fun k => j ∈ L k ∧ i ∈ R k) h_disj h_uniq (x i * x j)).symm
  · simp

/-- Linear map associated with Graham-Pollak bipartite decomposition. -/
def gpLinearMap (n m : ℕ) (L : Fin m → Finset (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (ℝ × (Fin m → ℝ)) where
  toFun x := (∑ i, x i, fun k => ∑ i ∈ L k, x i)
  map_add' x y := by ext <;> simp [sum_add_distrib]
  map_smul' c x := by ext <;> simp [mul_sum]

lemma gpLinearMap_injective (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) :
    Function.Injective (gpLinearMap n m L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h_sum_zero : ∑ i, x i = 0 := congr_arg Prod.fst hx
  have h_L_zero : ∀ k, ∑ i ∈ L k, x i = 0 := fun k => congr_fun (congr_arg Prod.snd hx) k
  have h_sq_id := sum_sq_identity n x
  have h_cross : (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0) = 0 := by
    rw [bipartite_sum_eq n m L R h x]
    exact sum_eq_zero (fun k _ => by rw [h_L_zero k, zero_mul])
  rw [h_sum_zero, h_cross] at h_sq_id
  norm_num at h_sq_id
  have h_sum_sq := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp h_sq_id.symm
  ext i
  exact sq_eq_zero_iff.mp (h_sum_sq i (mem_univ i))

/-- Main Theorem: Graham-Pollak Theorem (1971 / Tverberg 1982). -/
theorem graham_pollak (n m : ℕ) (L R : Fin m → Finset (Fin n))
    (h : IsCompleteBipartitePartition n m L R) :
    n - 1 ≤ m := by
  have hinj := gpLinearMap_injective n m L R h
  have h_rank := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_self] at h_rank
  omega

/-- The left vertex of the `k`-th star in the canonical star decomposition of $K_n$. -/
def starPartition_L (n : ℕ) (k : Fin (n - 1)) : Finset (Fin n) :=
  {⟨k.val, by have := k.isLt; omega⟩}

/-- The right vertices of the `k`-th star in the canonical star decomposition of $K_n$. -/
def starPartition_R (n : ℕ) (k : Fin (n - 1)) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => k.val < j.val)

@[simp] lemma mem_starPartition_L (n : ℕ) (k : Fin (n - 1)) (x : Fin n) :
    x ∈ starPartition_L n k ↔ x.val = k.val := by
  simp [starPartition_L]; exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

@[simp] lemma mem_starPartition_R (n : ℕ) (k : Fin (n - 1)) (x : Fin n) :
    x ∈ starPartition_R n k ↔ k.val < x.val := by
  simp [starPartition_R]

/-- Tightness of the Graham-Pollak Theorem:
$K_n$ can be partitioned into $n - 1$ complete bipartite graphs (specifically, stars). -/
theorem graham_pollak_tight (n : ℕ) :
    IsCompleteBipartitePartition n (n - 1) (starPartition_L n) (starPartition_R n) := by
  refine ⟨fun k => ?_, fun u v huv => ?_⟩
  · rw [disjoint_left]; simp; omega
  · rcases lt_trichotomy u.val v.val with hlt | heq | hgt
    · refine ⟨⟨u.val, by have := v.isLt; omega⟩, Or.inl (by simp [hlt]), ?_⟩
      rintro ⟨k, hk⟩ (⟨hkL, hkR⟩ | ⟨hkR, hkL⟩) <;> simp at hkL hkR
      · ext; exact hkL.symm
      · omega
    · exact False.elim (huv (Fin.ext heq))
    · refine ⟨⟨v.val, by have := u.isLt; omega⟩, Or.inr (by simp [hgt]), ?_⟩
      rintro ⟨k, hk⟩ (⟨hkL, hkR⟩ | ⟨hkR, hkL⟩) <;> simp at hkL hkR
      · omega
      · ext; exact hkL.symm
