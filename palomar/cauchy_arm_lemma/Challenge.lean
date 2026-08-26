import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-- A polygonal arm/chain of `n + 1` vertices in `ℝ × ℝ`. -/
def PolygonalChain (n : ℕ) := Fin (n + 1) → (ℝ × ℝ)

/-- Squared Euclidean distance between two points in `ℝ × ℝ`. -/
def distSq (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Dot product of two vectors in `ℝ × ℝ`. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Vector subtraction in `ℝ × ℝ`. -/
def vecSub (p q : ℝ × ℝ) : ℝ × ℝ := (p.1 - q.1, p.2 - q.2)

/-- Edge lengths match between two chains `P` and `Q`. -/
def EdgeLengthsMatch {n : ℕ} (P Q : PolygonalChain n) : Prop :=
  ∀ i : Fin n, distSq (P i.castSucc) (P i.succ) = distSq (Q i.castSucc) (Q i.succ)

/-- Opening of joint angles: dot product between outgoing unit-like vectors decreases (meaning angle increases). -/
def AnglesOpen {n : ℕ} (P Q : PolygonalChain n) : Prop :=
  ∀ i : Fin (n - 1),
    let i_prev : Fin (n + 1) := ⟨i.1, by omega⟩
    let i_curr : Fin (n + 1) := ⟨i.1 + 1, by omega⟩
    let i_next : Fin (n + 1) := ⟨i.1 + 2, by omega⟩
    dot (vecSub (P i_prev) (P i_curr)) (vecSub (P i_next) (P i_curr)) ≥
    dot (vecSub (Q i_prev) (Q i_curr)) (vecSub (Q i_next) (Q i_curr))

/-- **Cauchy's Arm Lemma (A. L. Cauchy, 1813):**
Opening the internal angles of a planar polygonal chain increases the Euclidean distance between
its endpoints for chains of length at most 2. -/
theorem cauchy_arm_lemma {n : ℕ} (hn : n ≤ 2) (P Q : PolygonalChain n)
    (h_len : EdgeLengthsMatch P Q) (h_ang : AnglesOpen P Q) :
    distSq (P 0) (P (Fin.last n)) ≤ distSq (Q 0) (Q (Fin.last n)) := sorry
