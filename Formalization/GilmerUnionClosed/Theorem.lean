import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Formalization.GilmerUnionClosed.Basic
import Formalization.GilmerUnionClosed.GoldenRatio
import Formalization.GilmerUnionClosed.Families

open scoped BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GilmerUnionClosed

/-!
# Frankl's Conjecture and Gilmer's Theorem Statements and Certificates

This module formalizes:
- The exact statement of Frankl's Union-Closed Sets Conjecture (`FranklConjectureStatement`).
- The exact statement of Gilmer's Theorem (`GilmerTheoremStatement`).
- The formal deduction `frankl_implies_gilmer`: any Frankl certificate implies a Gilmer certificate since $c_0 < 1/2$.
- Certified instances for two-element families and powerset families.
-/

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
    ∃ u ∈ familyUnion F, c₀ ≤ freq F u :=
  let ⟨u, hu, h_freq⟩ := hfrankl; ⟨u, hu, gilmerConstant_lt_half.le.trans h_freq⟩

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
