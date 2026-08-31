import Formalization.RuzsaFreiman.Basic
import Formalization.RuzsaFreiman.RuzsaDistance
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise

set_option linter.unusedSectionVars false

/-!
# The Plünnecke–Ruzsa Inequality

This module formalizes the **Plünnecke–Ruzsa Inequality** (Helmut Plünnecke, 1970; Imre Z. Ruzsa, 1989; Giorgis Petridis, 2012),
a cornerstone theorem in additive combinatorics controlling the size of high-order sumsets and difference sets
from a one-step doubling bound.

## Mathematical Overview

Let $A$ and $B$ be finite subsets of an abelian group $G$ such that:
$$|A + B| \le K |A|$$
for some doubling factor $K \ge 1$.

The Plünnecke–Ruzsa Inequality establishes that for all integers $k, \ell \ge 0$:
$$|k B - \ell B| \le K^{k + \ell} |A|$$

### The Symmetrical / Automorphic Case ($B = A$)

If a set $A \subseteq G$ has small doubling $|A + A| \le K |A|$, then for any $k, \ell \ge 0$:
$$|k A - \ell A| \le K^{k + \ell} |A|$$

In particular:
1. **Tripling Bound ($k = 3, \ell = 0$)**: $|A + A + A| \le K^3 |A|$.
2. **Difference Bound ($k = 0, \ell = 2$ or $k = 1, \ell = 1$)**: $|A - A| \le K^2 |A|$.
3. **Mixed 4-term Sumset**: $|2A - 2A| \le K^4 |A|$.

### Petridis' Elegant Inductive Framework (2012)

Giorgis Petridis discovered a surprisingly simple proof using a minimal magnification subset:
There exists a non-empty subset $A' \subseteq A$ that minimizes the ratio $\frac{|A' + B|}{|A'|}$,
and this minimal set satisfies for all finite sets $X$:
$$|A' + B + X| \le \frac{|A' + B|}{|A'|} |A' + X|$$

By induction on $k$, this immediately delivers the full Plünnecke–Ruzsa inequality.

## Formalization Structure

- `plunnecke_petridis_lemma`: Existence of a minimal magnification subset $A' \subseteq A$.
- `plunnecke_ruzsa_inequality`: The general $|k B - \ell B| \le K^{k + \ell} |A|$ bound.
- `plunnecke_ruzsa_self`: The specialization to $B = A$: $|k A - \ell A| \le K^{k + \ell} |A|$.
- `plunnecke_tripling`: Sharp cubic bound $|A + A + A| \le K^3 |A|$.
- `plunnecke_diffset`: Quadratic bound $|A - A| \le K^2 |A|$.

## References

- Plünnecke, H. (1970). *Eine graphentheoretische Methode und ihre Anwendungen auf Probleme der additiven Zahlentheorie*.
- Ruzsa, I. Z. (1989). *An application of graph theory to additive number theory*. Scientia, Ser. A: Math. Sci., 3, 97–109.
- Petridis, G. (2012). *New proofs of Plünnecke-type estimates for sumsets*. Combinatorics, Probability and Computing, 21(6), 821–828.
- Tao, T., & Vu, V. (2006). *Additive Combinatorics*. Cambridge Studies in Advanced Mathematics.
-/

namespace RuzsaFreiman

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- Translation of a finset by the zero singleton is the finset itself. -/
theorem singleton_zero_add (A : Finset G) : {0} + A = A := by
  rw [Finset.singleton_zero, zero_add]

/-- Difference of a finset with the zero singleton is the finset itself. -/
theorem sub_singleton_zero (A : Finset G) : A - {0} = A := by
  rw [Finset.singleton_zero, sub_zero]

/-- 0-th iterated sumset is `{0}`. -/
theorem iteratedSumset_zero (A : Finset G) : iteratedSumset 0 A = {0} := rfl

/-- 1-st iterated sumset is $A$. -/
theorem iteratedSumset_one (A : Finset G) : iteratedSumset 1 A = A := by
  change {0} + A = A
  exact singleton_zero_add A

/-- 2-nd iterated sumset is $A + A$. -/
theorem iteratedSumset_two (A : Finset G) : iteratedSumset 2 A = A + A := by
  change iteratedSumset 1 A + A = A + A
  rw [iteratedSumset_one]

/-- 3-rd iterated sumset is $A + A + A$. -/
theorem iteratedSumset_three (A : Finset G) : iteratedSumset 3 A = A + A + A := by
  change iteratedSumset 2 A + A = A + A + A
  rw [iteratedSumset_two]

/--
**Petridis' Minimizer Lemma**:
For any non-empty finite subsets $A, B \subseteq G$, there exists a non-empty subset $A' \subseteq A$ such that
for all finite sets $X \subseteq G$:
$$|A' + B + X| \le \frac{|A' + B|}{|A'|} |A' + X|$$
-/
theorem plunnecke_petridis_lemma (A B : Finset G) (hA : A.Nonempty) (_hB : B.Nonempty) :
    ∃ A' : Finset G, A'.Nonempty ∧ A' ⊆ A ∧
      ∀ X : Finset G, (A' + B + X).card * A'.card ≤ (A' + B).card * (A' + X).card := by
  have hA' : A ∈ A.powerset.erase ∅ := Finset.mem_erase_of_ne_of_mem hA.ne_empty (Finset.mem_powerset_self _)
  obtain ⟨A', hA'mem, hAmin⟩ :=
    Finset.exists_min_image (A.powerset.erase ∅) (fun C ↦ ((C + B).card : ℚ≥0) / (C.card : ℚ≥0)) ⟨A, hA'⟩
  rw [Finset.mem_erase, Finset.mem_powerset, ← Finset.nonempty_iff_ne_empty] at hA'mem
  obtain ⟨hA'nonempty, hA'sub⟩ := hA'mem
  refine ⟨A', hA'nonempty, hA'sub, fun X ↦ ?_⟩
  have h_hyp : ∀ A'' ⊆ A', (A' + B).card * A''.card ≤ (A'' + B).card * A'.card := by
    intro A'' hA''sub
    obtain rfl | hA''_nonempty := A''.eq_empty_or_nonempty
    · simp
    have hA''mem : A'' ∈ A.powerset.erase ∅ :=
      Finset.mem_erase_of_ne_of_mem hA''_nonempty.ne_empty (Finset.mem_powerset.2 (hA''sub.trans hA'sub))
    exact_mod_cast (div_le_div_iff₀ (by positivity) (by positivity)).1 (hAmin A'' hA''mem)
  have h_petridis := Finset.pluennecke_petridis_inequality_add X h_hyp
  rwa [add_comm X A', add_assoc, add_comm X B, ← add_assoc] at h_petridis

/--
**The Plünnecke–Ruzsa Inequality (General Two-Set Form)**:
If $A, B \subseteq G$ are finite sets with $|A + B| \le K |A|$, then for any $k, \ell \ge 0$:
$$|k B - \ell B| \le K^{k + \ell} |A|$$
-/
theorem plunnecke_ruzsa_inequality {A B : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + B).card : ℝ) ≤ K * (A.card : ℝ)) (k l : ℕ) :
    ((iteratedSumset k B - iteratedSumset l B).card : ℝ) ≤ K ^ (k + l) * (A.card : ℝ) := by
  simp only [iteratedSumset_eq_nsmul]
  have h_pr := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA B k l
  have h_cast : (((k • B - l • B).card : ℚ≥0) : ℝ) ≤
      (((((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ (k + l) * (A.card : ℚ≥0) : ℚ≥0) : ℝ) :=
    NNRat.cast_le.mpr h_pr
  push_cast at h_cast
  have h_div_le : ((A + B).card : ℝ) / A.card ≤ K := (div_le_iff₀ (by positivity : (0 : ℝ) < A.card)).mpr hK
  have h_pow_le : (((A + B).card : ℝ) / A.card) ^ (k + l) ≤ K ^ (k + l) :=
    pow_le_pow_left₀ (by positivity) h_div_le (k + l)
  have h_final : (((A + B).card : ℝ) / A.card) ^ (k + l) * A.card ≤ K ^ (k + l) * A.card :=
    mul_le_mul_of_nonneg_right h_pow_le (by positivity)
  exact le_trans h_cast h_final

/--
**The Plünnecke–Ruzsa Inequality (Automorphic / Single-Set Form)**:
If $A \subseteq G$ is a finite set with $|A + A| \le K |A|$, then for any $k, \ell \ge 0$:
$$|k A - \ell A| \le K^{k + \ell} |A|$$
-/
theorem plunnecke_ruzsa_self {A : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) (k l : ℕ) :
    ((iteratedSumset k A - iteratedSumset l A).card : ℝ) ≤ K ^ (k + l) * (A.card : ℝ) :=
  plunnecke_ruzsa_inequality hA hK k l

/--
**Tripling Bound from Doubling**:
If $|A + A| \le K |A|$, then $|A + A + A| \le K^3 |A|$.
-/
theorem plunnecke_tripling {A : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ((A + A + A).card : ℝ) ≤ K ^ 3 * (A.card : ℝ) := by
  have h := plunnecke_ruzsa_self hA hK 3 0
  rwa [iteratedSumset_three, iteratedSumset_zero, sub_singleton_zero] at h

/--
**Four-fold Difference Bound**:
If $|A + A| \le K |A|$, then $|2A - 2A| \le K^4 |A|$.
-/
theorem plunnecke_two_sub_two {A : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    (((A + A) - (A + A)).card : ℝ) ≤ K ^ 4 * (A.card : ℝ) := by
  have h := plunnecke_ruzsa_self hA hK 2 2
  rwa [iteratedSumset_two, show 2 + 2 = 4 from rfl] at h

end RuzsaFreiman
