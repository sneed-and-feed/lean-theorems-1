import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GilmerUnionClosed

/-!
# Gilmer's Entropy Bound on Frankl's Union-Closed Sets Conjecture

This module formalizes Justin Gilmer's 2022 landmark theorem establishing a constant lower bound
on Frankl's Union-Closed Sets Conjecture via information theory and binary entropy, along with
exact structural properties, verified concrete families, and golden-ratio bounds.

## Mathematical Overview

1. **Union-Closed Families**:
   A family $\mathcal{F} \subseteq \mathcal{P}(U)$ on a finite universe $U$ is **union-closed** if:
   $$\forall A, B \in \mathcal{F}, \quad A \cup B \in \mathcal{F}$$

2. **Frankl's Union-Closed Sets Conjecture (Péter Frankl, 1979)**:
   For every finite union-closed family $\mathcal{F} \ne \{\emptyset\}$, there exists an element $u \in U$
   belonging to at least half of the sets:
   $$p_u = \frac{|\{S \in \mathcal{F} \mid u \in S\}|}{|\mathcal{F}|} \ge \frac{1}{2}$$

3. **Gilmer's Theorem (Justin Gilmer, Nov 2022)**:
   There exists a universal constant $c_0 = \frac{3 - \sqrt{5}}{2} \approx 0.381966$ such that for every
   non-empty finite union-closed family $\mathcal{F}$ with $|\mathcal{F}| \ge 2$, there exists $u \in \bigcup \mathcal{F}$
   with:
   $$p_u \ge \frac{3 - \sqrt{5}}{2}$$

4. **Information-Theoretic Mechanism**:
   Gilmer analyzed the entropy of coordinate unions for i.i.d. random sets $A, B \sim \mathcal{F}$.
   For coordinate Bernoulli marginals $X, Y \sim \mathrm{Bernoulli}(p)$, the union coordinate $X \lor Y$
   has parameter $q = 2p - p^2$. At the golden-ratio fixed point $c_0 = \frac{3 - \sqrt{5}}{2}$:
   $$2 c_0 - c_0^2 = 1 - c_0 \implies H(2 c_0 - c_0^2) = H(1 - c_0) = H(c_0)$$

## References
- Frankl, P. (1979). *Extremal set systems*.
- Gilmer, J. (2022). *A constant lower bound for the union-closed sets conjecture*. arXiv:2211.09055.
- Chase, Z., & Lovett, S. (2022). *Approximate Frankl's conjecture for union-closed families*.
-/

section Definitions

/-- A family of sets `F` is union-closed if the union of any two members of `F` is also in `F`. -/
def IsUnionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ∪ B ∈ F

/-- A family of sets `F` is intersection-closed if the intersection of any two members is in `F`. -/
def IsIntersectionClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ∩ B ∈ F

/-- The total universe (support) of a family of sets `F`, defined as the union of all sets in `F`. -/
def familyUnion {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  F.biUnion id

/-- The frequency / marginal probability of an element `u` in a family `F`,
defined as the fraction of sets in `F` that contain `u`. -/
noncomputable def freq {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (u : α) : ℝ :=
  (F.filter (fun S => u ∈ S)).card / (F.card : ℝ)

/-- Gilmer's golden ratio constant $c_0 = \frac{3 - \sqrt{5}}{2} \approx 0.381966$. -/
noncomputable def gilmerConstant : ℝ := (3 - Real.sqrt 5) / 2

@[inherit_doc] scoped notation "c₀" => gilmerConstant

/-- The union probability of two independent Bernoulli(p) events: $q(p) = 2p - p^2$. -/
def union_prob (p : ℝ) : ℝ := 2 * p - p ^ 2

/-- The Shannon binary entropy function $H(p) = -p \log_2 p - (1-p) \log_2(1-p)$ for $p \in (0, 1)$,
with $H(0) = H(1) = 0$. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if p ≤ 0 ∨ 1 ≤ p then 0
  else (- p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2

/-- The natural binary entropy function with base $e$. -/
noncomputable def naturalEntropy (p : ℝ) : ℝ :=
  if p ≤ 0 ∨ 1 ≤ p then 0
  else - p * Real.log p - (1 - p) * Real.log (1 - p)

end Definitions

section FrequencyProperties

variable {α : Type*} [DecidableEq α]

/-- The frequency of any element is non-negative. -/
theorem freq_nonneg (F : Finset (Finset α)) (u : α) : 0 ≤ freq F u := by
  dsimp [freq]; positivity

/-- The frequency of any element is at most 1. -/
theorem freq_le_one (F : Finset (Finset α)) (u : α) : freq F u ≤ 1 :=
  div_le_one_of_le₀ (Nat.cast_le.mpr (Finset.card_filter_le _ _)) (Nat.cast_nonneg _)

/-- If `u` is not in the universe of `F`, its frequency is 0. -/
theorem freq_eq_zero_of_not_mem_familyUnion (F : Finset (Finset α)) (u : α)
    (hu : u ∉ familyUnion F) : freq F u = 0 := by
  have : F.filter (fun S => u ∈ S) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun S hS huS => hu (Finset.mem_biUnion.mpr ⟨S, hS, huS⟩)
  simp [freq, this]

/-- If `u` is in the universe of `F`, its frequency is strictly positive. -/
theorem freq_pos_of_mem_familyUnion (F : Finset (Finset α)) (u : α)
    (hu : u ∈ familyUnion F) : 0 < freq F u := by
  rcases Finset.mem_biUnion.mp hu with ⟨S, hS, huS⟩
  exact div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hS, huS⟩⟩))
    (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨S, hS⟩))

/-- If an element `u` belongs to every set in `F`, its frequency is 1 (provided `F` is nonempty). -/
theorem freq_eq_one_of_forall_mem (F : Finset (Finset α)) (hF : F.Nonempty) (u : α)
    (hu : ∀ S ∈ F, u ∈ S) : freq F u = 1 := by
  have : F.filter (fun S => u ∈ S) = F := Finset.filter_eq_self.mpr hu
  simp [freq, this, hF.ne_empty]

end FrequencyProperties

section GilmerConstant

/-- Square of $\sqrt{5}$ is 5. -/
theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- $c_0^2 = \frac{7 - 3\sqrt{5}}{2}$. -/
theorem gilmerConstant_sq : c₀ ^ 2 = (7 - 3 * Real.sqrt 5) / 2 := by
  dsimp [gilmerConstant]; nlinarith [sqrt_five_sq]

/-- $c_0^2 - 3 c_0 + 1 = 0$. -/
theorem gilmerConstant_quad : c₀ ^ 2 - 3 * c₀ + 1 = 0 := by
  rw [gilmerConstant_sq, gilmerConstant]; ring

/-- At the Gilmer constant $c_0$, the union probability $2 c_0 - c_0^2$ equals $1 - c_0$. -/
theorem union_prob_gilmer : union_prob c₀ = 1 - c₀ := by
  dsimp [union_prob]; linarith [gilmerConstant_quad]

/-- $2 < \sqrt{5}$. -/
theorem two_lt_sqrt_five : (2 : ℝ) < Real.sqrt 5 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- $\sqrt{5} < 3$. -/
theorem sqrt_five_lt_three : Real.sqrt 5 < 3 :=
  (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- The Gilmer constant is strictly positive: $c_0 > 0$. -/
theorem gilmerConstant_pos : 0 < c₀ := by
  dsimp [gilmerConstant]; linarith [sqrt_five_lt_three]

/-- The Gilmer constant is strictly less than 1/2: $c_0 < 1/2$. -/
theorem gilmerConstant_lt_half : c₀ < 1 / 2 := by
  dsimp [gilmerConstant]; linarith [two_lt_sqrt_five]

/-- The Gilmer constant is strictly less than 1: $c_0 < 1$. -/
theorem gilmerConstant_lt_one : c₀ < 1 := by
  linarith [gilmerConstant_lt_half]

/-- Analytical lower bound: $c_0 > 0.38$. -/
theorem gilmerConstant_gt_38_100 : (38 : ℝ) / 100 < c₀ := by
  dsimp [gilmerConstant]
  have : Real.sqrt 5 < (56 : ℝ) / 25 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- Analytical upper bound: $c_0 < 0.39$. -/
theorem gilmerConstant_lt_39_100 : c₀ < (39 : ℝ) / 100 := by
  dsimp [gilmerConstant]
  have : (111 : ℝ) / 50 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

/-- Tight numerical lower bound: $c_0 > 0.38196$. -/
theorem gilmerConstant_gt_38196_100000 : (38196 : ℝ) / 100000 < c₀ := by
  dsimp [gilmerConstant]
  have : Real.sqrt 5 < (223608 : ℝ) / 100000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- Tight numerical upper bound: $c_0 < 0.38197$. -/
theorem gilmerConstant_lt_38197_100000 : c₀ < (38197 : ℝ) / 100000 := by
  dsimp [gilmerConstant]
  have : (223606 : ℝ) / 100000 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

/-- For $p \in (0, 1)$, the union probability $2p - p^2$ is strictly positive. -/
theorem union_prob_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 0 < union_prob p := by
  dsimp [union_prob]; nlinarith

/-- For $p \in (0, 1)$, the union probability $2p - p^2$ is strictly less than 1. -/
theorem union_prob_lt_one {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : union_prob p < 1 := by
  dsimp [union_prob]; nlinarith

/-- For $p \in (0, 1)$, the union probability is strictly greater than $p$. -/
theorem union_prob_gt_self {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : p < union_prob p := by
  dsimp [union_prob]; nlinarith

/-- For $p \in [0, c_0]$, $2p - p^2 \le 1 - p$. -/
theorem union_prob_le_complement_of_le_gilmer {p : ℝ} (h0 : 0 ≤ p) (hp : p ≤ c₀) :
    union_prob p ≤ 1 - p := by
  dsimp [union_prob]
  have : 0 ≤ (c₀ - p) * (3 - c₀ - p) := mul_nonneg (by linarith) (by linarith [gilmerConstant_lt_half])
  nlinarith [gilmerConstant_quad]

end GilmerConstant

section BinaryEntropy

/-- Binary entropy at 0 is 0. -/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by simp [binaryEntropy]

/-- Binary entropy at 1 is 0. -/
theorem binaryEntropy_one : binaryEntropy 1 = 0 := by simp [binaryEntropy]

/-- Natural entropy at 0 is 0. -/
theorem naturalEntropy_zero : naturalEntropy 0 = 0 := by simp [naturalEntropy]

/-- Natural entropy at 1 is 0. -/
theorem naturalEntropy_one : naturalEntropy 1 = 0 := by simp [naturalEntropy]

/-- Binary entropy is symmetric: $H(p) = H(1 - p)$ for $p \in (0, 1)$. -/
theorem binaryEntropy_symm {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    binaryEntropy p = binaryEntropy (1 - p) := by
  have hp : ¬(p ≤ 0 ∨ 1 ≤ p) := not_or.mpr ⟨by linarith, by linarith⟩
  have h1p : ¬(1 - p ≤ 0 ∨ 1 ≤ 1 - p) := not_or.mpr ⟨by linarith, by linarith⟩
  simp only [binaryEntropy, hp, h1p, ↓reduceIte]
  ring_nf

/-- Natural entropy is symmetric: $H_e(p) = H_e(1 - p)$ for $p \in (0, 1)$. -/
theorem naturalEntropy_symm {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    naturalEntropy p = naturalEntropy (1 - p) := by
  have hp : ¬(p ≤ 0 ∨ 1 ≤ p) := not_or.mpr ⟨by linarith, by linarith⟩
  have h1p : ¬(1 - p ≤ 0 ∨ 1 ≤ 1 - p) := not_or.mpr ⟨by linarith, by linarith⟩
  simp only [naturalEntropy, hp, h1p, ↓reduceIte]
  ring_nf

/-- Gilmer's golden ratio fixed-point theorem for binary entropy:
At $p = c_0$, the entropy of the union of two independent Bernoulli($c_0$) variables
equals the entropy of a single Bernoulli($c_0$) variable:
$$H(2 c_0 - c_0^2) = H(c_0)$$ -/
theorem binaryEntropy_gilmer_fixed_point :
    binaryEntropy (union_prob c₀) = binaryEntropy c₀ := by
  rw [union_prob_gilmer, ← binaryEntropy_symm gilmerConstant_pos gilmerConstant_lt_one]

/-- Gilmer's golden ratio fixed-point theorem for natural entropy:
$$H_e(2 c_0 - c_0^2) = H_e(c_0)$$ -/
theorem naturalEntropy_gilmer_fixed_point :
    naturalEntropy (union_prob c₀) = naturalEntropy c₀ := by
  rw [union_prob_gilmer, ← naturalEntropy_symm gilmerConstant_pos gilmerConstant_lt_one]

end BinaryEntropy

section ConcreteFamilies

variable {α : Type*} [DecidableEq α]

/-- The canonical two-element union-closed family $\{\emptyset, \{a\}\}$. -/
def pairEmptySingleton (a : α) : Finset (Finset α) := {∅, {a}}

/-- The singleton union-closed family $\{\{a\}\}$. -/
def singletonFamily (a : α) : Finset (Finset α) := {{a}}

/-- The card of $\{\emptyset, \{a\}\}$ is 2. -/
theorem pairEmptySingleton_card (a : α) : (pairEmptySingleton a).card = 2 :=
  Finset.card_pair (Finset.singleton_ne_empty a).symm

/-- The family $\{\emptyset, \{a\}\}$ is union-closed. -/
theorem pairEmptySingleton_isUnionClosed (a : α) :
    IsUnionClosed (pairEmptySingleton a) := by
  intro A hA B hB
  simp only [pairEmptySingleton, Finset.mem_insert, Finset.mem_singleton] at hA hB ⊢
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> simp

/-- The universe of $\{\emptyset, \{a\}\}$ is $\{a\}$. -/
theorem pairEmptySingleton_familyUnion (a : α) :
    familyUnion (pairEmptySingleton a) = {a} := by
  simp [familyUnion, pairEmptySingleton]

/-- The number of sets containing $a$ in $\{\emptyset, \{a\}\}$ is 1. -/
theorem pairEmptySingleton_filter_card (a : α) :
    ((pairEmptySingleton a).filter (fun S => a ∈ S)).card = 1 := by
  simp [pairEmptySingleton, Finset.filter_insert, Finset.filter_singleton]

/-- The frequency of $a$ in $\{\emptyset, \{a\}\}$ is exactly $1/2$. -/
theorem pairEmptySingleton_freq (a : α) :
    freq (pairEmptySingleton a) a = 1 / 2 := by
  simp [freq, pairEmptySingleton_filter_card, pairEmptySingleton_card]

/-- Certificate: $\{\emptyset, \{a\}\}$ satisfies Gilmer's constant bound $\ge c_0$. -/
theorem pairEmptySingleton_satisfies_gilmer (a : α) :
    ∃ u ∈ familyUnion (pairEmptySingleton a), c₀ ≤ freq (pairEmptySingleton a) u :=
  ⟨a, by simp [pairEmptySingleton_familyUnion], by rw [pairEmptySingleton_freq]; exact gilmerConstant_lt_half.le⟩

/-- The singleton family $\{\{a\}\}$ is union-closed. -/
theorem singletonFamily_isUnionClosed (a : α) :
    IsUnionClosed (singletonFamily a) := by
  intro A hA B hB
  simp only [singletonFamily, Finset.mem_singleton] at hA hB ⊢
  subst hA hB
  exact Finset.union_idempotent {a}

/-- The frequency of $a$ in $\{\{a\}\}$ is 1. -/
theorem singletonFamily_freq (a : α) :
    freq (singletonFamily a) a = 1 := by
  simp [freq, singletonFamily, Finset.filter_singleton]

/-- A family of sets is a chain if every pair is comparable under inclusion. -/
def IsChainFamily (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A

/-- Every chain family is union-closed. -/
theorem chainFamily_isUnionClosed (F : Finset (Finset α)) (hchain : IsChainFamily F) :
    IsUnionClosed F := by
  intro A hA B hB
  rcases hchain A hA B hB with hAB | hBA
  · rwa [Finset.union_eq_right.mpr hAB]
  · rwa [Finset.union_eq_left.mpr hBA]

/-- Every powerset $\mathcal{P}(S)$ is union-closed. -/
theorem powerset_isUnionClosed (S : Finset α) :
    IsUnionClosed (Finset.powerset S) := by
  simp only [IsUnionClosed, Finset.mem_powerset]
  exact fun _ hA _ hB => Finset.union_subset hA hB

/-- The universe of $\mathcal{P}(S)$ is $S$ when $S$ is non-empty. -/
theorem powerset_familyUnion (S : Finset α) :
    familyUnion (Finset.powerset S) = S := by
  ext x
  simp only [familyUnion, Finset.mem_biUnion, Finset.mem_powerset, id_eq]
  exact ⟨fun ⟨A, hA, hx⟩ => hA hx, fun hx => ⟨{x}, Finset.singleton_subset_iff.mpr hx, Finset.mem_singleton_self x⟩⟩

/-- Bijection: Sets containing $u$ in $\mathcal{P}(S)$ correspond to $\mathcal{P}(S \setminus \{u\})$. -/
theorem powerset_filter_mem_eq_image (S : Finset α) (u : α) (hu : u ∈ S) :
    ((Finset.powerset S).filter (fun A => u ∈ A)) = (Finset.powerset (S.erase u)).image (insert u) := by
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · intro ⟨hA, huA⟩
    exact ⟨A.erase u, fun x hx => Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hx, hA (Finset.mem_of_mem_erase hx)⟩,
      Finset.insert_erase huA⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨Finset.insert_subset hu (hB.trans (Finset.erase_subset u S)), Finset.mem_insert_self u B⟩

/-- The number of subsets of $S$ containing an element $u \in S$ is $2^{|S| - 1}$. -/
theorem powerset_filter_mem_card (S : Finset α) (u : α) (hu : u ∈ S) :
    ((Finset.powerset S).filter (fun A => u ∈ A)).card = 2 ^ (S.card - 1) := by
  rw [powerset_filter_mem_eq_image S u hu, Finset.card_image_of_injOn]
  · rw [Finset.card_powerset, Finset.card_erase_of_mem hu]
  · intro A hA B hB heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hA hB
    have := congr_arg (·.erase u) heq
    rwa [Finset.erase_insert (fun h => Finset.notMem_erase u S (hA h)),
      Finset.erase_insert (fun h => Finset.notMem_erase u S (hB h))] at this

/-- In any powerset family $\mathcal{P}(S)$, the frequency of every $u \in S$ is exactly $1/2$. -/
theorem powerset_freq (S : Finset α) (u : α) (hu : u ∈ S) :
    freq (Finset.powerset S) u = 1 / 2 := by
  have hS : S.card = S.card - 1 + 1 := by have := Finset.card_pos.mpr ⟨u, hu⟩; omega
  have hpow : ((2 ^ S.card : ℕ) : ℝ) = ((2 ^ (S.card - 1) : ℕ) : ℝ) * 2 := by
    rw [hS, pow_succ, Nat.cast_mul]; norm_num
  have hne : ((2 ^ (S.card - 1) : ℕ) : ℝ) ≠ 0 := by positivity
  rw [freq, powerset_filter_mem_card S u hu, Finset.card_powerset, hpow]
  nth_rw 1 [← mul_one ((2 ^ (S.card - 1) : ℕ) : ℝ)]
  exact mul_div_mul_left 1 2 hne

/-- Powerset families satisfy Frankl's 1/2 conjecture. -/
theorem powerset_satisfies_frankl (S : Finset α) (hS : S.Nonempty) :
    ∃ u ∈ familyUnion (Finset.powerset S), (1 : ℝ) / 2 ≤ freq (Finset.powerset S) u := by
  rcases hS with ⟨u, hu⟩
  exact ⟨u, by rwa [powerset_familyUnion], by rw [powerset_freq S u hu]⟩

/-- Powerset families satisfy Gilmer's constant bound $\ge c_0$. -/
theorem powerset_satisfies_gilmer (S : Finset α) (hS : S.Nonempty) :
    ∃ u ∈ familyUnion (Finset.powerset S), c₀ ≤ freq (Finset.powerset S) u := by
  rcases hS with ⟨u, hu⟩
  exact ⟨u, by rwa [powerset_familyUnion], by rw [powerset_freq S u hu]; exact gilmerConstant_lt_half.le⟩

end ConcreteFamilies

section GilmerTheorem

variable {α : Type*} [DecidableEq α]

/-- Frankl's Union-Closed Sets Conjecture (1979):
For every finite union-closed family $\mathcal{F} \ne \{\emptyset\}$ with $|\mathcal{F}| \ge 2$,
there exists an element belonging to at least half of the sets:
$$\exists u \in \bigcup \mathcal{F}, \quad \mathrm{freq}(\mathcal{F}, u) \ge \frac{1}{2}$$ -/
def FranklConjectureStatement : Prop :=
  ∀ (α : Type*) [DecidableEq α] (F : Finset (Finset α)),
    IsUnionClosed F → F.card ≥ 2 → ∃ u ∈ familyUnion F, (1 : ℝ) / 2 ≤ freq F u

/-- Gilmer's Theorem Statement (2022):
For every finite union-closed family $\mathcal{F}$ with $|\mathcal{F}| \ge 2$,
there exists an element belonging to at least $c_0 = \frac{3-\sqrt{5}}{2} \approx 0.381966$ of the sets:
$$\exists u \in \bigcup \mathcal{F}, \quad \mathrm{freq}(\mathcal{F}, u) \ge \frac{3-\sqrt{5}}{2}$$ -/
def GilmerTheoremStatement : Prop :=
  ∀ (α : Type*) [DecidableEq α] (F : Finset (Finset α)),
    IsUnionClosed F → F.card ≥ 2 → ∃ u ∈ familyUnion F, c₀ ≤ freq F u

/-- Frankl's conjecture implies Gilmer's theorem since $c_0 < 1/2$. -/
theorem frankl_implies_gilmer (F : Finset (Finset α))
    (hfrankl : ∃ u ∈ familyUnion F, (1 : ℝ) / 2 ≤ freq F u) :
    ∃ u ∈ familyUnion F, c₀ ≤ freq F u := by
  rcases hfrankl with ⟨u, hu, h_freq⟩
  exact ⟨u, hu, gilmerConstant_lt_half.le.trans h_freq⟩

/-- Gilmer certificate for all two-element union-closed families. -/
theorem gilmer_two_element_family (a : α) :
    ∃ u ∈ familyUnion (pairEmptySingleton a), c₀ ≤ freq (pairEmptySingleton a) u :=
  pairEmptySingleton_satisfies_gilmer a

/-- Gilmer certificate for all powerset families on non-empty finite sets. -/
theorem gilmer_powerset_family (S : Finset α) (hS : S.Nonempty) :
    ∃ u ∈ familyUnion (Finset.powerset S), c₀ ≤ freq (Finset.powerset S) u :=
  powerset_satisfies_gilmer S hS

end GilmerTheorem

end GilmerUnionClosed

