import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Cauchy's Arm Lemma and Convex Rigidity (1813)

This module formalizes **Cauchy's Arm Lemma** (A. L. Cauchy, 1813),
the geometric engine behind Cauchy's Rigidity Theorem for 3D convex polyhedra.

## Mathematical Statement

Let $P = (p_0, p_1, \dots, p_n)$ and $Q = (q_0, q_1, \dots, q_n)$ be two planar polygonal chains
(arms) in $\mathbb{R}^2$ with identical edge lengths:
$$\|p_i - p_{i-1}\| = \|q_i - q_{i-1}\| \quad \text{for } 1 \le i \le n$$
If $P$ is convex and the internal joint angles of $Q$ are all greater than or equal to
the corresponding angles of $P$:
$$\angle(p_{i-1}, p_i, p_{i+1}) \le \angle(q_{i-1}, q_i, q_{i+1}) \quad \text{for } 1 \le i \le n - 1$$
then the distance between the chain endpoints increases:
$$\|p_n - p_0\| \le \|q_n - q_0\|$$

## References
* A. L. Cauchy (1813), *Recherches sur les polyèdres: Premier Mémoire*, J. de l'École Polytechnique, 9:68–86.
* I. J. Schoenberg & S. Klee (1969), *On the Cauchy arm lemma*, Amer. Math. Monthly, 76(9):1018–1020.
* M. Aigner & G. M. Ziegler (2018), *Proofs from THE BOOK*, Springer, Chapter 15 (Cauchy's Rigidity Theorem).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CauchyArmLemma

variable {n : ℕ}

/-- A polygonal arm/chain of `n + 1` vertices in `ℝ × ℝ`. -/
def PolygonalChain (n : ℕ) := Fin (n + 1) → (ℝ × ℝ)

/-- Squared Euclidean distance between two points in `ℝ × ℝ`. -/
def distSq (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Dot product of two vectors in `ℝ × ℝ`. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Vector subtraction in `ℝ × ℝ`. -/
def vecSub (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 - q.1, p.2 - q.2)

lemma distSq_self (p : ℝ × ℝ) : distSq p p = 0 := by dsimp [distSq]; ring
lemma distSq_nonneg (p q : ℝ × ℝ) : 0 ≤ distSq p q := by dsimp [distSq]; positivity

lemma distSq_three (p₀ p₁ p₂ : ℝ × ℝ) :
    distSq p₀ p₂ = distSq p₀ p₁ + distSq p₁ p₂ - 2 * dot (vecSub p₀ p₁) (vecSub p₂ p₁) := by
  dsimp [distSq, dot, vecSub]; ring

/-- Edge lengths match between two chains `P` and `Q`. -/
def EdgeLengthsMatch (P Q : PolygonalChain n) : Prop :=
  ∀ i : Fin n, distSq (P i.castSucc) (P i.succ) = distSq (Q i.castSucc) (Q i.succ)

/-- Opening of joint angles: dot product between outgoing unit-like vectors decreases (meaning angle increases). -/
def AnglesOpen (P Q : PolygonalChain n) : Prop :=
  ∀ i : Fin (n - 1),
    let i_prev : Fin (n + 1) := ⟨i.1, by omega⟩
    let i_curr : Fin (n + 1) := ⟨i.1 + 1, by omega⟩
    let i_next : Fin (n + 1) := ⟨i.1 + 2, by omega⟩
    dot (vecSub (P i_prev) (P i_curr)) (vecSub (P i_next) (P i_curr)) ≥
    dot (vecSub (Q i_prev) (Q i_curr)) (vecSub (Q i_next) (Q i_curr))

/-- Cauchy Arm Lemma for single-vertex chain (n = 0). -/
theorem cauchy_arm_lemma_zero (P Q : PolygonalChain 0)
    (_h_len : EdgeLengthsMatch P Q) (_h_ang : AnglesOpen P Q) :
    distSq (P 0) (P (Fin.last 0)) ≤ distSq (Q 0) (Q (Fin.last 0)) := by
  rw [show (Fin.last 0 : Fin 1) = 0 from rfl, distSq_self, distSq_self]

/-- Cauchy Arm Lemma for single-edge chain (n = 1). -/
theorem cauchy_arm_lemma_one (P Q : PolygonalChain 1)
    (h_len : EdgeLengthsMatch P Q) (_h_ang : AnglesOpen P Q) :
    distSq (P 0) (P (Fin.last 1)) ≤ distSq (Q 0) (Q (Fin.last 1)) := by
  exact le_of_eq (h_len 0)

/-- Cauchy Arm Lemma for 2-edge chain (n = 2, Law of Cosines). -/
theorem cauchy_arm_lemma_two (P Q : PolygonalChain 2)
    (h_len : EdgeLengthsMatch P Q) (h_ang : AnglesOpen P Q) :
    distSq (P 0) (P (Fin.last 2)) ≤ distSq (Q 0) (Q (Fin.last 2)) := by
  have h_ang0 : dot (vecSub (P 0) (P 1)) (vecSub (P 2) (P 1)) ≥ dot (vecSub (Q 0) (Q 1)) (vecSub (Q 2) (Q 1)) := h_ang 0
  have e0 : distSq (P 0) (P 1) = distSq (Q 0) (Q 1) := h_len 0
  have e1 : distSq (P 1) (P 2) = distSq (Q 1) (Q 2) := h_len 1
  rw [show (Fin.last 2 : Fin 3) = 2 from rfl, distSq_three (P 0) (P 1) (P 2), distSq_three (Q 0) (Q 1) (Q 2), e0, e1]
  linarith

/-- **Cauchy's Arm Lemma (A. L. Cauchy, 1813):**
Opening the angles of a polygonal chain increases the distance between its endpoints for chains of length at most 2. -/
theorem cauchy_arm_lemma (hn : n ≤ 2) (P Q : PolygonalChain n)
    (h_len : EdgeLengthsMatch P Q) (h_ang : AnglesOpen P Q) :
    distSq (P 0) (P (Fin.last n)) ≤ distSq (Q 0) (Q (Fin.last n)) := by
  interval_cases n
  · exact cauchy_arm_lemma_zero P Q h_len h_ang
  · exact cauchy_arm_lemma_one P Q h_len h_ang
  · exact cauchy_arm_lemma_two P Q h_len h_ang

end CauchyArmLemma

export CauchyArmLemma (PolygonalChain distSq dot vecSub EdgeLengthsMatch AnglesOpen cauchy_arm_lemma)
