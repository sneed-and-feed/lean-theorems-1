import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GilmerUnionClosed

/-!
# Gilmer's Golden Ratio Constant, Union Probability, and Binary Entropy

This module formalizes:
- Gilmer's constant $c_0 = \frac{3 - \sqrt{5}}{2} \approx 0.381966$.
- The union probability $q(p) = 2p - p^2$ for Bernoulli marginals.
- Algebraic properties ($c_0^2 - 3c_0 + 1 = 0$, $2c_0 - c_0^2 = 1 - c_0$).
- Analytical and tight numerical bounds ($0.38196 < c_0 < 0.38197$).
- Binary entropy $H(p)$ and natural entropy $H_e(p)$ functions.
- Entropy symmetry $H(p) = H(1 - p)$.
- Gilmer's golden ratio fixed-point theorems: $H(2 c_0 - c_0^2) = H(c_0)$ and $H_e(2 c_0 - c_0^2) = H_e(c_0)$.
-/

section Definitions

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
theorem gilmerConstant_lt_one : c₀ < 1 :=
  gilmerConstant_lt_half.trans (by norm_num)

/-- Analytical lower bound: $c_0 > 0.38$. -/
theorem gilmerConstant_gt_38_100 : (38 : ℝ) / 100 < c₀ := by
  have : Real.sqrt 5 < (56 : ℝ) / 25 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp [gilmerConstant]; linarith

/-- Analytical upper bound: $c_0 < 0.39$. -/
theorem gilmerConstant_lt_39_100 : c₀ < (39 : ℝ) / 100 := by
  have : (111 : ℝ) / 50 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  dsimp [gilmerConstant]; linarith

/-- Tight numerical lower bound: $c_0 > 0.38196$. -/
theorem gilmerConstant_gt_38196_100000 : (38196 : ℝ) / 100000 < c₀ := by
  have : Real.sqrt 5 < (223608 : ℝ) / 100000 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp [gilmerConstant]; linarith

/-- Tight numerical upper bound: $c_0 < 0.38197$. -/
theorem gilmerConstant_lt_38197_100000 : c₀ < (38197 : ℝ) / 100000 := by
  have : (223606 : ℝ) / 100000 < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  dsimp [gilmerConstant]; linarith

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
  have : 0 ≤ (c₀ - p) * (3 - c₀ - p) := mul_nonneg (by linarith) (by linarith [gilmerConstant_lt_half])
  dsimp [union_prob]; nlinarith [gilmerConstant_quad]

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
    binaryEntropy (union_prob c₀) = binaryEntropy c₀ :=
  union_prob_gilmer ▸ (binaryEntropy_symm gilmerConstant_pos gilmerConstant_lt_one).symm

/-- Gilmer's golden ratio fixed-point theorem for natural entropy:
$$H_e(2 c_0 - c_0^2) = H_e(c_0)$$ -/
theorem naturalEntropy_gilmer_fixed_point :
    naturalEntropy (union_prob c₀) = naturalEntropy c₀ :=
  union_prob_gilmer ▸ (naturalEntropy_symm gilmerConstant_pos gilmerConstant_lt_one).symm

end BinaryEntropy

end GilmerUnionClosed
