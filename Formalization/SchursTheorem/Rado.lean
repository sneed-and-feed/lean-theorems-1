import Formalization.SchursTheorem.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

open Finset

/-!
# Single-Equation Rado Partition Regularity & Linear Systems

This module formalizes the single-equation theory of **Rado's Theorem** (Richard Rado, 1933)
and its connections to **Schur's Theorem** and arithmetic progressions.

## Mathematical Context & Overview

In his 1933 dissertation (*Studien zur Kombinatorik*), Richard Rado characterized exactly which
systems of homogeneous linear equations are partition regular over the positive integers $\mathbb{N}^+$.

For a single homogeneous linear equation
$$\sum_{i=0}^{k-1} c_i x_i = 0 \quad (c_i \in \mathbb{Z} \setminus \{0\}),$$
**Rado's Single-Equation Theorem** asserts that the equation is partition regular over $\mathbb{N}^+$
if and only if there exists a non-empty subset of indices $I \subseteq \{0, \dots, k-1\}$ such that
$$\sum_{i \in I} c_i = 0.$$

### Constant-Solution Zero-Sum vs. Non-Zero-Sum Equations

Rado's condition bifurcates naturally into two fundamentally distinct regimes:
1. **Zero-Sum Case ($\sum_{i=0}^{k-1} c_i = 0$)**:
   When the entire coefficient vector sums to zero, the equation admits an explicit constant
   monochromatic solution $x = (m, m, \dots, m)$ for any $m \ge 1$, since $\sum c_i m = m \sum c_i = 0$.
   Hence, every zero-sum linear equation is partition regular over $\mathbb{N}^+$ with trivial cutoff $N = 1$.

2. **Non-Zero-Sum Case ($\sum c_i \ne 0$ with $\sum_{i \in I} c_i = 0$ for some $I \subsetneq \{0, \dots, k-1\}$)**:
   In this case, no constant vector can solve the equation. Proving partition regularity requires
   significantly deeper Ramsey-theoretic machinery (such as Deuber's $(m, p, c)$-sets, van der Waerden's
   theorem on arithmetic progressions, or graph Ramsey reductions). Schur's equation $x + y - z = 0$
   is the prototypical example, where the full sum is $1 + 1 - 1 = 1 \ne 0$ but the sub-sum $c_0 + c_2 = 0$
   vanishes, and partition regularity is established via multicolor graph Ramsey triangles.

### Key Results Formalized in this Module:

1. **Constant-Solution Zero-Sum Corollary to Rado's Theorem (Theorem 1)**:
   Zero-sum linear equations $\sum c_i = 0$ are partition regular via constant solutions $x = (1, \dots, 1)$.

2. **Schur's Equation as a Rado Equation (Theorem 2)**:
   The Schur equation $x + y = z$ with $c_{\text{Schur}} = (1, 1, -1)$ satisfies Rado's sub-sum condition ($c_0 + c_2 = 0$).
   Using `SchursTheorem.schurs_theorem`, we deduce partition regularity on $\mathbb{N}^+$ (`schur_is_rado_regular`)
   with explicit finite interval cutoff $B_r = \text{ramseyTriangleBound } r$ (`schur_interval_bound`).

3. **3-Term Arithmetic Progressions (Theorem 3)**:
   The 3-AP equation $x_0 - 2 x_1 + x_2 = 0$ corresponds to $c_{\text{AP3}} = (1, -2, 1)$, with $\sum c_i = 0$.
   Its partition regularity follows directly from the zero-sum corollary.

4. **4-Variable Additive Balance Equation**:
   The equation $x_0 + x_1 = x_2 + x_3$ with $c = (1, 1, -1, -1)$ has $\sum c_i = 0$ and is partition regular.

## Bound Fidelity Note (Anti-Pattern Q)

Following Palomar editorial standards, all docstrings and identifiers explicitly distinguish
between the recursive upper bound $B_r = \text{ramseyTriangleBound } r$ and the exact canonical
extremal Schur / Ramsey numbers $S(r)$ and $R_r(3)$.

## Main Definitions & Results

* `SchursTheorem.IsLinearSol`: Predicate for $\sum c_i x_i = 0$.
* `SchursTheorem.IsMonoSol`: Predicate for monochromaticity $\chi(x_i) = \chi(x_0)$.
* `SchursTheorem.HasNonzeroMonoSol`: Existence of monochromatic solution in $\mathbb{N}^+$.
* `SchursTheorem.HasDistinctMonoSol`: Existence of mutually distinct monochromatic solution in $\mathbb{N}^+$.
* `SchursTheorem.HasIntervalMonoSol`: Existence of monochromatic solution in $\{1, \dots, N\}$.
* `SchursTheorem.RadoSingleEquationCondition`: Non-empty zero sub-sum criterion $\exists I \ne \emptyset, \sum_{i \in I} c_i = 0$.
* `SchursTheorem.rado_zero_sum_partition_regular`: Theorem 1 (Constant-solution zero-sum corollary to Rado's theorem).
* `SchursTheorem.rado_zero_sum_interval`: Finite interval version for zero-sum equations.
* `SchursTheorem.schurCoeffs`: Schur coefficient vector $(1, 1, -1)$.
* `SchursTheorem.schurCoeffs_satisfies_rado`: Proof that Schur coefficients satisfy Rado's condition.
* `SchursTheorem.schur_is_rado_regular`: Theorem 2 (Schur partition regularity over $\mathbb{N}^+$).
* `SchursTheorem.schur_interval_bound`: Schur finite interval bound with $B_r = \text{ramseyTriangleBound } r$.
* `SchursTheorem.ap3Coeffs`: 3-AP coefficient vector $(1, -2, 1)$.
* `SchursTheorem.ap3_is_rado_regular`: Theorem 3 (3-AP partition regularity).
-/

namespace SchursTheorem

variable {k : ℕ}

/-! ### 1. Linear Homogeneous Equation & Monochromatic Solutions API -/

/-- A vector `x : Fin k → ℕ` is a linear solution to the homogeneous equation `∑ c_i x_i = 0`. -/
def IsLinearSol (c : Fin k → ℤ) (x : Fin k → ℕ) : Prop :=
  (∑ i : Fin k, c i * (x i : ℤ)) = 0

/-- A vector `x : Fin k → ℕ` is monochromatic under a coloring `χ : ℕ → Fin r`. -/
def IsMonoSol {r : ℕ} [NeZero k] (χ : ℕ → Fin r) (x : Fin k → ℕ) : Prop :=
  ∀ i : Fin k, χ (x i) = χ (x 0)

/-- An equation `c` has a non-zero monochromatic solution over positive integers $\mathbb{N}^+$. -/
def HasNonzeroMonoSol {r : ℕ} [NeZero k] (c : Fin k → ℤ) (χ : ℕ → Fin r) : Prop :=
  ∃ x : Fin k → ℕ, (∀ i, 1 ≤ x i) ∧ IsLinearSol c x ∧ IsMonoSol χ x

/-- An equation `c` has a distinct monochromatic solution over positive integers $\mathbb{N}^+$. -/
def HasDistinctMonoSol {r : ℕ} [NeZero k] (c : Fin k → ℤ) (χ : ℕ → Fin r) : Prop :=
  ∃ x : Fin k → ℕ, (∀ i, 1 ≤ x i) ∧ (∀ i j, i ≠ j → x i ≠ x j) ∧ IsLinearSol c x ∧ IsMonoSol χ x

/-- An equation `c` has a monochromatic solution bounded in the finite interval $\{1, \dots, N\}$. -/
def HasIntervalMonoSol {r : ℕ} [NeZero k] (c : Fin k → ℤ) (χ : ℕ → Fin r) (N : ℕ) : Prop :=
  ∃ x : Fin k → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ N) ∧ IsLinearSol c x ∧ IsMonoSol χ x

/-- An equation `c` has a distinct monochromatic solution bounded in $\{1, \dots, N\}$. -/
def HasIntervalDistinctMonoSol {r : ℕ} [NeZero k] (c : Fin k → ℤ) (χ : ℕ → Fin r) (N : ℕ) : Prop :=
  ∃ x : Fin k → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ N) ∧ (∀ i j, i ≠ j → x i ≠ x j) ∧ IsLinearSol c x ∧ IsMonoSol χ x

/-- Bounded interval monochromatic solution implies non-zero monochromatic solution. -/
lemma HasIntervalMonoSol.toHasNonzeroMonoSol {r : ℕ} [NeZero k] {c : Fin k → ℤ} {χ : ℕ → Fin r} {N : ℕ}
    (h : HasIntervalMonoSol c χ N) : HasNonzeroMonoSol c χ :=
  let ⟨x, hx, hlin, hmono⟩ := h; ⟨x, fun i => (hx i).1, hlin, hmono⟩

/-- Bounded interval distinct monochromatic solution implies distinct monochromatic solution. -/
lemma HasIntervalDistinctMonoSol.toHasDistinctMonoSol {r : ℕ} [NeZero k] {c : Fin k → ℤ} {χ : ℕ → Fin r} {N : ℕ}
    (h : HasIntervalDistinctMonoSol c χ N) : HasDistinctMonoSol c χ :=
  let ⟨x, hx, hdist, hlin, hmono⟩ := h; ⟨x, fun i => (hx i).1, hdist, hlin, hmono⟩

/-- Interval distinct monochromatic solution implies interval monochromatic solution. -/
lemma HasIntervalDistinctMonoSol.toHasIntervalMonoSol {r : ℕ} [NeZero k] {c : Fin k → ℤ} {χ : ℕ → Fin r} {N : ℕ}
    (h : HasIntervalDistinctMonoSol c χ N) : HasIntervalMonoSol c χ N :=
  let ⟨x, hx, _, hlin, hmono⟩ := h; ⟨x, hx, hlin, hmono⟩

/-- Monotonicity of interval solutions under interval expansion $M \le N$. -/
lemma HasIntervalMonoSol.mono {r : ℕ} [NeZero k] {c : Fin k → ℤ} {χ : ℕ → Fin r} {M N : ℕ}
    (h : HasIntervalMonoSol c χ M) (hMN : M ≤ N) : HasIntervalMonoSol c χ N :=
  let ⟨x, hx, hlin, hmono⟩ := h; ⟨x, fun i => ⟨(hx i).1, (hx i).2.trans hMN⟩, hlin, hmono⟩

/-- Pairwise monochromaticity is equivalent to index-0 monochromaticity for non-empty index types. -/
lemma isMonoSol_iff_pairwise {r : ℕ} [NeZero k] (χ : ℕ → Fin r) (x : Fin k → ℕ) :
    IsMonoSol χ x ↔ ∀ i j : Fin k, χ (x i) = χ (x j) :=
  ⟨fun h i j => (h i).trans (h j).symm, fun h i => h i 0⟩

/-- Constant vector is monochromatic under any coloring. -/
lemma isMonoSol_const {r : ℕ} [NeZero k] (χ : ℕ → Fin r) (m : ℕ) :
    IsMonoSol χ (fun (_ : Fin k) => m) :=
  fun _ => rfl

/-- Linear evaluation on a constant vector factorizes out the constant. -/
lemma isLinearSol_const (c : Fin k → ℤ) (m : ℕ) (h_sum : ∑ i : Fin k, c i = 0) :
    IsLinearSol c (fun (_ : Fin k) => m) := by
  simp [IsLinearSol, ← Finset.sum_mul, h_sum]

/-! ### 2. Rado's Zero-Sum Criterion (Theorem 1: Zero-Sum Regularity) -/

/-- **Rado's Single-Equation Condition**:
A single homogeneous linear equation $c : \text{Fin } k \to \mathbb{Z}$ satisfies Rado's condition
if there exists a non-empty subset $I \subseteq \text{Fin } k$ whose coefficients sum to zero:
$$\exists \emptyset \ne I \subseteq \{0,\dots,k-1\}, \sum_{i \in I} c_i = 0.$$

### Mathematical Context:
Rado's 1933 theorem proves that this condition is both necessary and sufficient for the partition
regularity of $\sum c_i x_i = 0$ over $\mathbb{N}^+$.
* **Zero-sum case ($\sum_{i=0}^{k-1} c_i = 0$)**: Admits constant monochromatic solutions $x = (m,\dots,m)$
  since $\sum c_i m = m \sum c_i = 0$.
* **Non-zero-sum case ($\sum c_i \ne 0$ with $\sum_{i \in I} c_i = 0$)**: No constant solution exists;
  proving partition regularity requires deeper combinatorial and Ramsey-theoretic machinery
  (e.g., Deuber's $(m, p, c)$-sets, van der Waerden's theorem, or graph Ramsey reductions). -/
def RadoSingleEquationCondition (c : Fin k → ℤ) : Prop :=
  ∃ I : Finset (Fin k), I.Nonempty ∧ ∑ i ∈ I, c i = 0

/-- Any coefficient vector whose full sum is zero satisfies Rado's condition. -/
lemma rado_condition_of_zero_sum [NeZero k] (c : Fin k → ℤ) (h_sum : ∑ i : Fin k, c i = 0) :
    RadoSingleEquationCondition c :=
  ⟨Finset.univ, Finset.univ_nonempty, h_sum⟩

/-- **Constant-Solution Zero-Sum Corollary to Rado's Theorem**:
Every integer coefficient vector $c : \text{Fin } k \to \mathbb{Z}$ whose full coefficients sum to zero
($\sum_{i=0}^{k-1} c_i = 0$) is partition regular over $\mathbb{N}^+$.

The proof constructs an explicit constant monochromatic solution $x = (1, \dots, 1)$, which satisfies
$\sum c_i \cdot 1 = \sum c_i = 0$ and is monochromatic under any coloring.
(For non-zero-sum equations satisfying Rado's condition $\sum_{i \in I} c_i = 0$ for $I \subsetneq \{0,\dots,k-1\}$,
constant solutions fail and deeper Ramsey machinery such as Deuber / van der Waerden is required.) -/
theorem rado_zero_sum_partition_regular (k : ℕ) [NeZero k] (c : Fin k → ℤ)
    (h_sum : ∑ i : Fin k, c i = 0) (r : ℕ) (_hr : 1 ≤ r) (χ : ℕ → Fin r) :
    HasNonzeroMonoSol c χ :=
  ⟨fun _ => 1, fun _ => le_rfl, isLinearSol_const c 1 h_sum, isMonoSol_const χ 1⟩

/-- **Constant-Solution Zero-Sum Corollary to Rado's Theorem (Explicit Index Size Formulation)**:
Variant of `rado_zero_sum_partition_regular` taking an explicit `1 ≤ k` hypothesis instead of typeclass `[NeZero k]`. -/
theorem rado_zero_sum_partition_regular_of_le (k : ℕ) (hk : 1 ≤ k) (c : Fin k → ℤ)
    (h_sum : ∑ i : Fin k, c i = 0) (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    letI : NeZero k := ⟨by omega⟩
    HasNonzeroMonoSol c χ :=
  letI : NeZero k := ⟨by omega⟩
  rado_zero_sum_partition_regular k c h_sum r hr χ

/-- **Rado's Zero-Sum Criterion (Finite Interval Cutoff)**:
For any zero-sum equation and any cutoff $N \ge 1$, there exists a monochromatic solution
in $\{1, \dots, N\}$. -/
theorem rado_zero_sum_interval (k : ℕ) [NeZero k] (c : Fin k → ℤ)
    (h_sum : ∑ i : Fin k, c i = 0) (r : ℕ) (_hr : 1 ≤ r) (χ : ℕ → Fin r)
    (N : ℕ) (hN : 1 ≤ N) :
    HasIntervalMonoSol c χ N :=
  ⟨fun _ => 1, fun _ => ⟨le_rfl, hN⟩, isLinearSol_const c 1 h_sum, isMonoSol_const χ 1⟩

/-- Scaled monochromatic solution for zero-sum equations at any positive integer base $m \ge 1$. -/
theorem rado_zero_sum_scaled (k : ℕ) [NeZero k] (c : Fin k → ℤ)
    (h_sum : ∑ i : Fin k, c i = 0) (r : ℕ) (_hr : 1 ≤ r) (χ : ℕ → Fin r) (m : ℕ) (_hm : 1 ≤ m) :
    ∃ x : Fin k → ℕ, (∀ i, m ≤ x i ∧ x i ≤ m) ∧ IsLinearSol c x ∧ IsMonoSol χ x :=
  ⟨fun _ => m, fun _ => ⟨le_rfl, le_rfl⟩, isLinearSol_const c m h_sum, isMonoSol_const χ m⟩

/-! ### 3. Schur's Equation as a Rado Equation (Theorem 2: Schur 3-Variable Reduction) -/

/-- The coefficient vector of Schur's equation $x + y - z = 0$: $c = (1, 1, -1)$. -/
def schurCoeffs : Fin 3 → ℤ := ![(1 : ℤ), 1, -1]

@[simp]
lemma schurCoeffs_zero : schurCoeffs 0 = 1 := rfl

@[simp]
lemma schurCoeffs_one : schurCoeffs 1 = 1 := rfl

@[simp]
lemma schurCoeffs_two : schurCoeffs 2 = -1 := rfl

/-- The total sum of Schur coefficients is $1 + 1 - 1 = 1$. -/
lemma sum_schurCoeffs : ∑ i : Fin 3, schurCoeffs i = 1 := by
  simp [Fin.sum_univ_three, schurCoeffs]

/-- The Schur coefficient vector is NOT zero-sum: $\sum c_i = 1 \ne 0$. -/
lemma sum_schurCoeffs_ne_zero : ∑ i : Fin 3, schurCoeffs i ≠ 0 := by
  rw [sum_schurCoeffs]; decide

/-- The sub-sum $c_0 + c_2 = 1 + (-1) = 0$ vanishes. -/
lemma schur_subsum_zero : schurCoeffs 0 + schurCoeffs 2 = 0 := rfl

/-- Schur's coefficient vector satisfies Rado's single-equation condition via $I = \{0, 2\}$. -/
theorem schurCoeffs_satisfies_rado : RadoSingleEquationCondition schurCoeffs :=
  ⟨{0, 2}, ⟨0, by simp⟩, by rw [Finset.sum_pair (by decide)]; rfl⟩

/-- Linear solution to Schur's equation is equivalent to $x_0 + x_1 = x_2$. -/
lemma isLinearSol_schurCoeffs_iff (x : Fin 3 → ℕ) :
    IsLinearSol schurCoeffs x ↔ (x 0 : ℤ) + (x 1 : ℤ) = (x 2 : ℤ) := by
  simp [IsLinearSol, Fin.sum_univ_three, schurCoeffs]; omega

/-- Natural addition characterization of Schur linear solutions. -/
lemma isLinearSol_schurCoeffs_nat (x : Fin 3 → ℕ) :
    IsLinearSol schurCoeffs x ↔ x 0 + x 1 = x 2 := by
  simp [IsLinearSol, Fin.sum_univ_three, schurCoeffs]; omega

/-- Monochromatic solution vector characterization for 3 variables. -/
lemma isMonoSol_three_iff {r : ℕ} (χ : ℕ → Fin r) (x : Fin 3 → ℕ) :
    IsMonoSol χ x ↔ χ (x 1) = χ (x 0) ∧ χ (x 2) = χ (x 0) :=
  ⟨fun h => ⟨h 1, h 2⟩, fun ⟨h1, h2⟩ i => by fin_cases i <;> simp [*]⟩

/-- **Schur's Theorem as Rado Regularity with Explicit Ramsey Bound (Theorem 2)**:
For any $r \ge 1$ and cutoff $N = \text{ramseyTriangleBound } r$, every $r$-coloring
contains a monochromatic solution to $c_{\text{Schur}}$ in $\{1, \dots, N\}$.
Note: `ramseyTriangleBound r` is the explicit upper bound $B_r \ge R_r(3)$ (Anti-Pattern Q). -/
theorem schur_interval_bound (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    HasIntervalMonoSol schurCoeffs χ (ramseyTriangleBound r) := by
  obtain ⟨c, x, y, z, hx1, hy1, hz1, hxN, hyN, hzN, hxyz, hcx, hcy, hcz⟩ := schurs_theorem r hr χ
  refine ⟨![x, y, z], ?_, by simp [isLinearSol_schurCoeffs_nat, hxyz], ?_⟩
  · intro i; fin_cases i <;> exact ⟨by assumption, by assumption⟩
  · rw [isMonoSol_three_iff]; exact ⟨hcy.trans hcx.symm, hcz.trans hcx.symm⟩

/-- **Schur Partition Regularity on Positive Integers**:
The Schur equation $x + y = z$ is partition regular over the positive integers $\mathbb{N}^+$:
for any $r$-coloring $\chi : ℕ \to \text{Fin } r$, there exists a positive monochromatic solution.
For the quantitative finite interval cutoff $N = \text{ramseyTriangleBound } r$, see `schur_interval_bound`
and `SchursTheorem.schurs_theorem`. -/
theorem schur_is_rado_regular (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    HasNonzeroMonoSol schurCoeffs χ :=
  (schur_interval_bound r hr χ).toHasNonzeroMonoSol

/-- Interval monotonicity: Schur monochromatic solutions exist for any $N \ge \text{ramseyTriangleBound } r$. -/
theorem schur_interval_bound_of_le (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) (N : ℕ)
    (hN : ramseyTriangleBound r ≤ N) :
    HasIntervalMonoSol schurCoeffs χ N :=
  (schur_interval_bound r hr χ).mono hN

/-- The $z$-coordinate of any Schur solution in $\mathbb{N}^+$ is strictly larger than $x$ and $y$. -/
lemma schur_sol_z_gt (x : Fin 3 → ℕ) (h_sol : IsLinearSol schurCoeffs x) (h_pos : ∀ i, 1 ≤ x i) :
    x 0 < x 2 ∧ x 1 < x 2 := by
  rw [isLinearSol_schurCoeffs_nat] at h_sol
  have h0 := h_pos 0; have h1 := h_pos 1; omega

/-- Distinctness criterion: if $x_0 \ne x_1$, then all 3 variables in a Schur solution are distinct. -/
lemma schur_sol_distinct_of_ne (x : Fin 3 → ℕ) (h_sol : IsLinearSol schurCoeffs x)
    (h_pos : ∀ i, 1 ≤ x i) (hne : x 0 ≠ x 1) :
    ∀ i j : Fin 3, i ≠ j → x i ≠ x j := by
  have ⟨hz0, hz1⟩ := schur_sol_z_gt x h_sol h_pos
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | contradiction | exact hne | exact hne.symm | exact ne_of_lt hz0 |
            exact (ne_of_lt hz0).symm | exact ne_of_lt hz1 | exact (ne_of_lt hz1).symm

/-! ### 4. 3-Term Arithmetic Progression Equation as a Rado Equation (Theorem 3) -/

/-- The coefficient vector of the 3-AP equation $x_0 - 2 x_1 + x_2 = 0$: $c = (1, -2, 1)$. -/
def ap3Coeffs : Fin 3 → ℤ := ![(1 : ℤ), -2, 1]

@[simp] lemma ap3Coeffs_zero : ap3Coeffs 0 = 1 := rfl
@[simp] lemma ap3Coeffs_one : ap3Coeffs 1 = -2 := rfl
@[simp] lemma ap3Coeffs_two : ap3Coeffs 2 = 1 := rfl

/-- The sum of 3-AP coefficients is $1 + (-2) + 1 = 0$. -/
lemma sum_ap3Coeffs : ∑ i : Fin 3, ap3Coeffs i = 0 := by
  simp [Fin.sum_univ_three, ap3Coeffs]

/-- The 3-AP coefficient vector satisfies Rado's condition. -/
theorem ap3Coeffs_satisfies_rado : RadoSingleEquationCondition ap3Coeffs :=
  rado_condition_of_zero_sum ap3Coeffs sum_ap3Coeffs

/-- Linear solution to 3-AP equation is equivalent to $x_0 + x_2 = 2 x_1$. -/
lemma isLinearSol_ap3Coeffs_iff (x : Fin 3 → ℕ) :
    IsLinearSol ap3Coeffs x ↔ (x 0 : ℤ) + (x 2 : ℤ) = 2 * (x 1 : ℤ) := by
  simp [IsLinearSol, Fin.sum_univ_three, ap3Coeffs]; omega

/-- Natural arithmetic characterization of 3-AP linear solutions. -/
lemma isLinearSol_ap3Coeffs_nat (x : Fin 3 → ℕ) :
    IsLinearSol ap3Coeffs x ↔ x 0 + x 2 = 2 * x 1 := by
  simp [IsLinearSol, Fin.sum_univ_three, ap3Coeffs]; omega

/-- **3-AP Zero-Sum Reduction (Theorem 3: 3-AP Regularity)**:
The 3-term arithmetic progression equation is partition regular over $\mathbb{N}^+$. -/
theorem ap3_is_rado_regular (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    HasNonzeroMonoSol ap3Coeffs χ :=
  rado_zero_sum_partition_regular 3 ap3Coeffs sum_ap3Coeffs r hr χ

/-- Finite interval bound for 3-AP: monochromatic 3-AP solution in $\{1, \dots, N\}$ for any $N \ge 1$. -/
theorem ap3_interval_bound (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) (N : ℕ) (hN : 1 ≤ N) :
    HasIntervalMonoSol ap3Coeffs χ N :=
  rado_zero_sum_interval 3 ap3Coeffs sum_ap3Coeffs r hr χ N hN

/-- Monochromatic 3-term progression: $a, a + d, a + 2d$ of the same color. -/
def IsMonoAP3 {r : ℕ} (χ : ℕ → Fin r) (a d : ℕ) : Prop :=
  χ a = χ (a + d) ∧ χ (a + d) = χ (a + 2 * d)

/-- Any monochromatic solution to `ap3Coeffs` with $x_0 \le x_1$ generates a monochromatic 3-AP. -/
theorem monoAP3_of_monoSol {r : ℕ} (χ : ℕ → Fin r) (x : Fin 3 → ℕ)
    (h_lin : IsLinearSol ap3Coeffs x) (h_mono : IsMonoSol χ x) (h_le : x 0 ≤ x 1) :
    IsMonoAP3 χ (x 0) (x 1 - x 0) := by
  rw [isLinearSol_ap3Coeffs_nat] at h_lin
  rw [isMonoSol_three_iff] at h_mono
  have hd : x 0 + (x 1 - x 0) = x 1 := by omega
  have h2d : x 0 + 2 * (x 1 - x 0) = x 2 := by omega
  exact ⟨by rw [hd]; exact h_mono.1.symm, by rw [hd, h2d]; exact h_mono.1.trans h_mono.2.symm⟩

/-- Trivial monochromatic 3-AP with difference $d = 0$ for any starting value $a \ge 1$. -/
theorem exists_mono_ap3_trivial (r : ℕ) (_hr : 1 ≤ r) (χ : ℕ → Fin r) (a : ℕ) (ha : 1 ≤ a) :
    1 ≤ a ∧ IsMonoAP3 χ a 0 :=
  ⟨ha, rfl, rfl⟩

/-! ### 5. 4-Variable Additive Balance Equation -/

/-- The coefficient vector of the 4-variable equation $x_0 + x_1 - x_2 - x_3 = 0$: $c = (1, 1, -1, -1)$. -/
def add4Coeffs : Fin 4 → ℤ := ![(1 : ℤ), 1, -1, -1]

@[simp] lemma add4Coeffs_zero : add4Coeffs 0 = 1 := rfl
@[simp] lemma add4Coeffs_one : add4Coeffs 1 = 1 := rfl
@[simp] lemma add4Coeffs_two : add4Coeffs 2 = -1 := rfl
@[simp] lemma add4Coeffs_three : add4Coeffs 3 = -1 := rfl

/-- The sum of coefficients for $x_0 + x_1 = x_2 + x_3$ vanishes. -/
lemma sum_add4Coeffs : ∑ i : Fin 4, add4Coeffs i = 0 := by
  simp [Fin.sum_univ_four, add4Coeffs]

/-- The 4-variable equation satisfies Rado's condition. -/
theorem add4Coeffs_satisfies_rado : RadoSingleEquationCondition add4Coeffs :=
  rado_condition_of_zero_sum add4Coeffs sum_add4Coeffs

/-- Linear solution to 4-variable equation is equivalent to $x_0 + x_1 = x_2 + x_3$. -/
lemma isLinearSol_add4Coeffs_nat (x : Fin 4 → ℕ) :
    IsLinearSol add4Coeffs x ↔ x 0 + x 1 = x 2 + x 3 := by
  simp [IsLinearSol, Fin.sum_univ_four, add4Coeffs]; omega

/-- Partition regularity of $x_0 + x_1 = x_2 + x_3$ over $\mathbb{N}^+$. -/
theorem add4_is_rado_regular (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) :
    HasNonzeroMonoSol add4Coeffs χ :=
  rado_zero_sum_partition_regular 4 add4Coeffs sum_add4Coeffs r hr χ

/-- Finite interval bound for 4-variable additive equation: solution in $\{1, \dots, N\}$ for any $N \ge 1$. -/
theorem add4_interval_bound (r : ℕ) (hr : 1 ≤ r) (χ : ℕ → Fin r) (N : ℕ) (hN : 1 ≤ N) :
    HasIntervalMonoSol add4Coeffs χ N :=
  rado_zero_sum_interval 4 add4Coeffs sum_add4Coeffs r hr χ N hN

#print axioms rado_zero_sum_partition_regular
#print axioms rado_zero_sum_interval
#print axioms schur_interval_bound
#print axioms schur_is_rado_regular
#print axioms ap3_is_rado_regular
#print axioms ap3_interval_bound
#print axioms add4_is_rado_regular
#print axioms add4_interval_bound

end SchursTheorem

