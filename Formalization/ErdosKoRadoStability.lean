import Formalization.ErdosKoRado
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Finset

/-!
# Erdős–Ko–Rado Equality Cases and Hilton–Milner Stability (1961, 1967)

This module formalizes the **uniqueness of extremal families** in the **Erdős–Ko–Rado Theorem**
and the **Hilton–Milner Stability Theorem** (A. J. W. Hilton & E. C. Milner, 1967).

## Mathematical Statement

Let $\alpha$ be an $n$-element universe with $n > 2k$ and $k \ge 1$.
Let $\mathcal{F} \subseteq \binom{\alpha}{k}$ be an intersecting family of $k$-element subsets:
$$\forall A, B \in \mathcal{F}, \quad A \cap B \ne \emptyset$$

### 1. EKR Uniqueness (Star Characterization)
When $n > 2k$, the maximum size $|\mathcal{F}| = \binom{n-1}{k-1}$ is achieved **uniquely** by **star families**
(also known as canonically centered families / pencils):
$$\mathcal{S}_x = \left\{ A \in \binom{\alpha}{k} \;\middle|\; x \in A \right\} \quad \text{for some fixed } x \in \alpha$$

### 2. Hilton–Milner Stability Theorem (1967)
If $\mathcal{F}$ is an intersecting family of $k$-element subsets of an $n$-element set ($n > 2k$)
that is **not a star** ($\bigcap_{A \in \mathcal{F}} A = \emptyset$), then its size is strictly bounded by:
$$|\mathcal{F}| \le \binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$$

This bound is sharp, attained by the **Hilton–Milner construction**:
For a fixed $k$-set $B \subset \alpha$ and a fixed element $x \in \alpha \setminus B$,
$$\mathcal{H}(x, B) = \{B\} \cup \left\{ A \in \binom{\alpha}{k} \;\middle|\; x \in A \wedge A \cap B \ne \emptyset \right\}$$

## References
* Erdős, P., Ko, C., & Rado, R. (1961). *Intersection theorems for systems of finite sets*. Quart. J. Math. Oxford, 12(1), 313–320.
* Hilton, A. J. W., & Milner, E. C. (1967). *Some intersection theorems for systems of finite sets*. Quart. J. Math. Oxford, 18(1), 369–384.
* Frankl, P. (1978). *On intersecting families of finite sets*. J. Combin. Theory Ser. A, 24(2), 146–161.
-/

namespace ErdosKoRadoStability

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================================================
-- Section 1: Star Families & Intersection Centers
-- ============================================================================

/-- A family `F` of sets is a star (canonically centered) if all sets share a common element `x`. -/
def IsStarFamily (F : Finset (Finset α)) : Prop :=
  ∃ x : α, ∀ A ∈ F, x ∈ A

/-- The full star family centered at `x` among all `k`-subsets of `α`. -/
def starFamily (x : α) (k : ℕ) : Finset (Finset α) :=
  ((Finset.univ : Finset α).powersetCard k).filter (fun A => x ∈ A)

/-- The cardinality of any full star family on an `n`-element set is `Nat.choose (n - 1) (k - 1)`. -/
lemma card_starFamily {n k : ℕ} (hn : Fintype.card α = n) (hk : 1 ≤ k) (hkn : k ≤ n) (x : α) :
    (starFamily x k).card = Nat.choose (n - 1) (k - 1) := by
  sorry

-- ============================================================================
-- Section 2: EKR Uniqueness Theorem (n > 2k)
-- ============================================================================

/-- **EKR Uniqueness Theorem (Erdős–Ko–Rado 1961):**
    For $n > 2k$, every intersecting family of $k$-sets achieving the maximal cardinality
    $\binom{n-1}{k-1}$ is necessarily a star family. -/
theorem erdos_ko_rado_uniqueness {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 1 ≤ k) (h2k : 2 * k < n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (h_max : F.card = Nat.choose (n - 1) (k - 1)) :
    IsStarFamily F := by
  sorry

-- ============================================================================
-- Section 3: Hilton–Milner Bound (EKR Stability)
-- ============================================================================

/-- The Hilton–Milner extremal bound: $\binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$. -/
def hiltonMilnerBound (n k : ℕ) : ℕ :=
  Nat.choose (n - 1) (k - 1) - Nat.choose (n - k - 1) (k - 1) + 1

/-- **Hilton–Milner Theorem (1967):**
    Let $n > 2k$ and $k \ge 2$. If $\mathcal{F}$ is an intersecting family of $k$-element subsets
    of an $n$-element universe that is NOT a star family, then
    $|\mathcal{F}| \le \binom{n-1}{k-1} - \binom{n-k-1}{k-1} + 1$. -/
theorem hilton_milner_stability {n k : ℕ}
    (hn : Fintype.card α = n) (hk : 2 ≤ k) (h2k : 2 * k < n)
    (F : Finset (Finset α))
    (hF_k : ∀ A ∈ F, A.card = k)
    (h_inter : ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B)
    (h_not_star : ¬ IsStarFamily F) :
    F.card ≤ hiltonMilnerBound n k := by
  sorry

end ErdosKoRadoStability
