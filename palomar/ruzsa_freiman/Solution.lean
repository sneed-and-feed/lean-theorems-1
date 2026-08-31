import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Pointwise
open scoped BigOperators Finset

set_option linter.unusedSectionVars false

namespace RuzsaFreiman

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The sumset $A + B = \{a + b : a \in A, b \in B\}$. -/
def sumset (A B : Finset G) : Finset G := A + B

/-- The difference set $A - B = \{a - b : a \in A, b \in B\}$. -/
def diffset (A B : Finset G) : Finset G := A - B

/-- The doubling constant $\sigma(A) = \frac{|A + A|}{|A|}$. -/
def doublingConstant (A : Finset G) : ℚ :=
  (A + A).card / (A.card : ℚ)

/-- The difference constant $\delta(A) = \frac{|A - A|}{|A|}$. -/
def differenceConstant (A : Finset G) : ℚ :=
  (A - A).card / (A.card : ℚ)

/-- Doubling constant is at least 1 for non-empty sets. -/
theorem doublingConstant_ge_one {A : Finset G} (hA : A.Nonempty) :
    1 ≤ doublingConstant A := by
  dsimp [doublingConstant]
  rw [one_le_div₀ (by positivity)]
  exact_mod_cast Finset.card_le_card_add_right hA

/-- Iterated sumset $k A = A + \dots + A$ ($k$ terms). -/
def iteratedSumset (k : ℕ) (A : Finset G) : Finset G :=
  match k with
  | 0 => {0}
  | k + 1 => iteratedSumset k A + A

/-- Equivalence between `iteratedSumset` and pointwise `nsmul`. -/
theorem iteratedSumset_eq_nsmul (k : ℕ) (A : Finset G) :
    iteratedSumset k A = k • A := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iteratedSumset, ih, succ_nsmul]

/-- The Ruzsa multiplicative ratio $\rho_R(A, B) = \frac{|A - B|}{\sqrt{|A| |B|}}$. -/
noncomputable def ruzsaRatio (A B : Finset G) : ℝ :=
  (A - B).card / Real.sqrt ((A.card : ℝ) * (B.card : ℝ))

/-- The Ruzsa distance $d_R(A, B) = \log \frac{|A - B|}{\sqrt{|A| |B|}}$. -/
noncomputable def ruzsaDistance (A B : Finset G) : ℝ :=
  Real.log (ruzsaRatio A B)

/-- Difference set has same size under reflection: $|A - B| = |B - A|$. -/
theorem card_diffset_symm (A B : Finset G) :
    (A - B).card = (B - A).card := by
  rw [← Finset.card_neg, neg_sub]

/-- Symmetry of the Ruzsa distance: $d_R(A, B) = d_R(B, A)$. -/
theorem ruzsaDistance_symm (A B : Finset G) :
    ruzsaDistance A B = ruzsaDistance B A := by
  dsimp [ruzsaDistance, ruzsaRatio]
  rw [card_diffset_symm A B, mul_comm (A.card : ℝ)]

/--
**Ruzsa Triangle Inequality (Cardinality Form)**:
For any finite subsets $A, B, C$ in an additive group $G$:
$$|B| \cdot |A - C| \le |A - B| \cdot |B - C|$$
-/
theorem ruzsa_triangle_cardinality (A B C : Finset G) :
    B.card * (A - C).card ≤ (A - B).card * (B - C).card := by
  have h := Finset.ruzsa_triangle_inequality_sub_sub_sub A B C
  rw [mul_comm B.card, card_diffset_symm B C]
  exact h

/-- Strict positivity of the Ruzsa multiplicative ratio for non-empty sets. -/
theorem ruzsaRatio_pos {A B : Finset G} (hA : A.Nonempty) (hB : B.Nonempty) :
    0 < ruzsaRatio A B := by
  have : (A - B).Nonempty := hA.sub hB
  dsimp [ruzsaRatio]
  positivity

/-- Multiplicative triangle inequality for the Ruzsa ratio. -/
theorem ruzsaRatio_mul_le {A B C : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    ruzsaRatio A C ≤ ruzsaRatio A B * ruzsaRatio B C := by
  dsimp [ruzsaRatio]
  have h_card : (B.card : ℝ) * (A - C).card ≤ (A - B).card * (B - C).card := by
    exact_mod_cast ruzsa_triangle_cardinality A B C
  have h_sqrt (X Y : Finset G) : Real.sqrt ((X.card : ℝ) * (Y.card : ℝ)) = Real.sqrt X.card * Real.sqrt Y.card :=
    Real.sqrt_mul (Nat.cast_nonneg _) _
  have hB_self : Real.sqrt B.card * Real.sqrt B.card = B.card := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have h_denom : Real.sqrt A.card * Real.sqrt B.card * (Real.sqrt B.card * Real.sqrt C.card) =
      (B.card : ℝ) * (Real.sqrt A.card * Real.sqrt C.card) := by
    linear_combination Real.sqrt A.card * Real.sqrt C.card * hB_self
  rw [div_mul_div_comm, h_sqrt A B, h_sqrt B C, h_sqrt A C, h_denom,
    ← mul_div_mul_left _ _ (ne_of_gt (by positivity : (0 : ℝ) < B.card))]
  exact div_le_div_of_nonneg_right h_card (by positivity)

/--
**Ruzsa Triangle Inequality (Metric Form)**:
For any non-empty finite subsets $A, B, C \subseteq G$:
$$d_R(A, C) \le d_R(A, B) + d_R(B, C)$$
-/
theorem ruzsa_triangle_inequality {A B C : Finset G}
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty) :
    ruzsaDistance A C ≤ ruzsaDistance A B + ruzsaDistance B C := by
  dsimp [ruzsaDistance]
  rw [← Real.log_mul (ne_of_gt (ruzsaRatio_pos hA hB)) (ne_of_gt (ruzsaRatio_pos hB hC))]
  exact Real.log_le_log (ruzsaRatio_pos hA hC) (ruzsaRatio_mul_le hA hB hC)

/--
**Iterated Difference Bound**:
For any non-empty finite set $A \subseteq G$ with $|A + A| \le K |A|$,
$|A - A| \le K^2 |A|$.
-/
theorem diffset_bound_of_doubling {A : Finset G} (hA : A.Nonempty) {K : ℝ}
    (hK : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    ((A - A).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
  have h_pos : (0 : ℝ) < A.card := by positivity
  have h_ineq : ((A - A).card : ℝ) * A.card ≤ ((A + A).card : ℝ) * (A + A).card := by
    exact_mod_cast Finset.ruzsa_triangle_inequality_sub_add_add A A A
  exact (mul_le_mul_iff_of_pos_right h_pos).mp (by nlinarith)

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

/-- A Generalized Arithmetic Progression (GAP) of dimension `dim` in an additive group $G$. -/
structure GAP (G : Type*) [AddCommGroup G] where
  dim : ℕ
  base : G
  steps : Fin dim → G
  lengths : Fin dim → ℕ

/-- The Finset of elements represented by a GAP $P$. -/
def gapElements (P : GAP G) : Finset G :=
  (Fintype.piFinset (fun i : Fin P.dim => Finset.range (P.lengths i))).image
    (fun (k : Fin P.dim → ℕ) => P.base + ∑ i : Fin P.dim, (k i) • (P.steps i))

/-- The cardinality of a GAP is bounded by the volume (product of side lengths). -/
theorem gapElements_card_le (P : GAP G) :
    (gapElements P).card ≤ ∏ i : Fin P.dim, P.lengths i := by
  dsimp [gapElements]
  exact Finset.card_image_le.trans (by simp)

/-- A map $\phi : A \to B$ is a Freiman homomorphism of order $k$ if it preserves $k$-term equality of sums. -/
def IsFreimanHomomorphism {H : Type*} [AddCommGroup H]
    (A : Finset G) (f : G → H) (k : ℕ) : Prop :=
  ∀ (xs ys : Fin k → G), (∀ i, xs i ∈ A) → (∀ i, ys i ∈ A) →
    (∑ i, xs i = ∑ i, ys i) → (∑ i, f (xs i) = ∑ i, f (ys i))

/-- Identity map is always a Freiman homomorphism of any order $k$. -/
theorem freimanHomomorphism_id (A : Finset G) (k : ℕ) :
    IsFreimanHomomorphism A id k :=
  fun _ _ _ _ => id

end RuzsaFreiman
