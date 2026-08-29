import UniverseAdelic.BinaryIcosahedral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open scoped Quaternion goldenRatio Classical Real BigOperators
open Real

/-- Helper character function on real parts $a = \operatorname{re}(u) \in [-1, 1]$. -/
def chi_re (l : ℕ) (a : ℝ) : ℝ :=
  if a = 1 then
    (l + 1 : ℝ)
  else if a = -1 then
    (-1 : ℝ) ^ l * (l + 1 : ℝ)
  else
    Real.sin ((l + 1 : ℝ) * Real.arccos a) / Real.sin (Real.arccos a)

/-- Character $\chi_\ell : ℍ[ℝ]^\times \to ℝ$ of the irreducible $\mathrm{SU}(2)$
representation of degree $\ell \in \mathbb{N}$ (dimension $\ell + 1$). -/
def chi (l : ℕ) (u : ℍ[ℝ]ˣ) : ℝ :=
  chi_re l (u : ℍ[ℝ]).re

lemma chi_one (l : ℕ) : chi l 1 = (l + 1 : ℝ) := by
  simp only [chi, chi_re]
  have : ((1 : ℍ[ℝ]ˣ) : ℍ[ℝ]).re = 1 := rfl
  rw [this]
  simp

lemma chi_centralInv (l : ℕ) : chi l centralInv = (-1 : ℝ) ^ l * (l + 1 : ℝ) := by
  simp only [chi, chi_re]
  have : (centralInv : ℍ[ℝ]).re = -1 := rfl
  rw [this]
  have h1 : (-1 : ℝ) ≠ 1 := by norm_num
  simp [h1]

/-- The decomposition of the character sum over the binary icosahedral group into its 9 conjugacy classes. -/
axiom sum_chi_binaryIcosahedral (l : ℕ) :
    ∑ g ∈ binaryIcosahedralFinset, chi l g =
      chi l 1 +
      chi l centralInv +
      30 * chi_re l 0 +
      20 * chi_re l (1 / 2) +
      20 * chi_re l (-1 / 2) +
      12 * chi_re l (φ / 2) +
      12 * chi_re l (-φ / 2) +
      12 * chi_re l (φ⁻¹ / 2) +
      12 * chi_re l (-φ⁻¹ / 2)

/-- Molien's character projection formula for the dimension of the $I^*$-invariant subspace
in the irreducible representation of degree $\ell$:
$$m_\ell = \frac{1}{120} \sum_{g \in I^*} \chi_\ell(g)$$ -/
def m (l : ℕ) : ℝ :=
  (1 / 120 : ℝ) * ∑ g ∈ binaryIcosahedralFinset, chi l g

/-- Golden ratio fundamental identity: $\phi - \phi^{-1} = 1$. -/
lemma phi_sub_phi_inv : φ - φ⁻¹ = 1 := by
  have h_inv : φ⁻¹ = φ - 1 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  linarith

/-! ### Character Evaluations at Conjugacy Classes -/

axiom chi_re_zero_0 : chi_re 0 0 = 1
axiom chi_re_zero_half : chi_re 0 (1 / 2) = 1
axiom chi_re_zero_neg_half : chi_re 0 (-1 / 2) = 1
axiom chi_re_zero_phi_half : chi_re 0 (φ / 2) = 1
axiom chi_re_zero_neg_phi_half : chi_re 0 (-φ / 2) = 1
axiom chi_re_zero_phi_inv_half : chi_re 0 (φ⁻¹ / 2) = 1
axiom chi_re_zero_neg_phi_inv_half : chi_re 0 (-φ⁻¹ / 2) = 1

axiom chi_re_one_0 : chi_re 1 0 = 0
axiom chi_re_one_half : chi_re 1 (1 / 2) = 1
axiom chi_re_one_neg_half : chi_re 1 (-1 / 2) = -1
axiom chi_re_one_phi_half : chi_re 1 (φ / 2) = φ
axiom chi_re_one_neg_phi_half : chi_re 1 (-φ / 2) = -φ
axiom chi_re_one_phi_inv_half : chi_re 1 (φ⁻¹ / 2) = φ⁻¹
axiom chi_re_one_neg_phi_inv_half : chi_re 1 (-φ⁻¹ / 2) = -φ⁻¹

axiom chi_re_two_0 : chi_re 2 0 = -1
axiom chi_re_two_half : chi_re 2 (1 / 2) = 0
axiom chi_re_two_neg_half : chi_re 2 (-1 / 2) = 0
axiom chi_re_two_phi_half : chi_re 2 (φ / 2) = φ
axiom chi_re_two_neg_phi_half : chi_re 2 (-φ / 2) = φ
axiom chi_re_two_phi_inv_half : chi_re 2 (φ⁻¹ / 2) = -φ⁻¹
axiom chi_re_two_neg_phi_inv_half : chi_re 2 (-φ⁻¹ / 2) = -φ⁻¹

axiom chi_re_three_0 : chi_re 3 0 = 0
axiom chi_re_three_half : chi_re 3 (1 / 2) = -1
axiom chi_re_three_neg_half : chi_re 3 (-1 / 2) = 1
axiom chi_re_three_phi_half : chi_re 3 (φ / 2) = 1
axiom chi_re_three_neg_phi_half : chi_re 3 (-φ / 2) = -1
axiom chi_re_three_phi_inv_half : chi_re 3 (φ⁻¹ / 2) = -1
axiom chi_re_three_neg_phi_inv_half : chi_re 3 (-φ⁻¹ / 2) = 1

axiom chi_re_four_0 : chi_re 4 0 = 1
axiom chi_re_four_half : chi_re 4 (1 / 2) = -1
axiom chi_re_four_neg_half : chi_re 4 (-1 / 2) = -1
axiom chi_re_four_phi_half : chi_re 4 (φ / 2) = 0
axiom chi_re_four_neg_phi_half : chi_re 4 (-φ / 2) = 0
axiom chi_re_four_phi_inv_half : chi_re 4 (φ⁻¹ / 2) = 0
axiom chi_re_four_neg_phi_inv_half : chi_re 4 (-φ⁻¹ / 2) = 0

axiom chi_re_five_0 : chi_re 5 0 = 0
axiom chi_re_five_half : chi_re 5 (1 / 2) = 0
axiom chi_re_five_neg_half : chi_re 5 (-1 / 2) = 0
axiom chi_re_five_phi_half : chi_re 5 (φ / 2) = -1
axiom chi_re_five_neg_phi_half : chi_re 5 (-φ / 2) = 1
axiom chi_re_five_phi_inv_half : chi_re 5 (φ⁻¹ / 2) = 1
axiom chi_re_five_neg_phi_inv_half : chi_re 5 (-φ⁻¹ / 2) = -1

axiom chi_re_six_0 : chi_re 6 0 = -1
axiom chi_re_six_half : chi_re 6 (1 / 2) = 1
axiom chi_re_six_neg_half : chi_re 6 (-1 / 2) = 1
axiom chi_re_six_phi_half : chi_re 6 (φ / 2) = -φ
axiom chi_re_six_neg_phi_half : chi_re 6 (-φ / 2) = -φ
axiom chi_re_six_phi_inv_half : chi_re 6 (φ⁻¹ / 2) = φ⁻¹
axiom chi_re_six_neg_phi_inv_half : chi_re 6 (-φ⁻¹ / 2) = φ⁻¹

axiom chi_re_twelve_0 : chi_re 12 0 = 1
axiom chi_re_twelve_half : chi_re 12 (1 / 2) = 1
axiom chi_re_twelve_neg_half : chi_re 12 (-1 / 2) = 1
axiom chi_re_twelve_phi_half : chi_re 12 (φ / 2) = φ
axiom chi_re_twelve_neg_phi_half : chi_re 12 (-φ / 2) = φ
axiom chi_re_twelve_phi_inv_half : chi_re 12 (φ⁻¹ / 2) = -φ⁻¹
axiom chi_re_twelve_neg_phi_inv_half : chi_re 12 (-φ⁻¹ / 2) = -φ⁻¹

/-! ### Proofs of Multiplicities $m_\ell$ -/

/-- $m_0 = 1$: The trivial representation is invariant under $I^*$. -/
theorem m_zero : m 0 = 1 := by
  rw [m, sum_chi_binaryIcosahedral 0]
  rw [chi_one 0, chi_centralInv 0]
  rw [chi_re_zero_0, chi_re_zero_half, chi_re_zero_neg_half]
  rw [chi_re_zero_phi_half, chi_re_zero_neg_phi_half, chi_re_zero_phi_inv_half, chi_re_zero_neg_phi_inv_half]
  ring

/-- $m_1 = 0$: No spin-1/2 invariants in $I^*$. -/
theorem m_one : m 1 = 0 := by
  rw [m, sum_chi_binaryIcosahedral 1]
  rw [chi_one 1, chi_centralInv 1]
  rw [chi_re_one_0, chi_re_one_half, chi_re_one_neg_half]
  rw [chi_re_one_phi_half, chi_re_one_neg_phi_half, chi_re_one_phi_inv_half, chi_re_one_neg_phi_inv_half]
  ring

/-- $m_2 = 0$: No spin-1 (vector) invariants in $I^*$. -/
theorem m_two : m 2 = 0 := by
  rw [m, sum_chi_binaryIcosahedral 2]
  rw [chi_one 2, chi_centralInv 2]
  rw [chi_re_two_0, chi_re_two_half, chi_re_two_neg_half]
  rw [chi_re_two_phi_half, chi_re_two_neg_phi_half, chi_re_two_phi_inv_half, chi_re_two_neg_phi_inv_half]
  have h_phi := phi_sub_phi_inv
  linear_combination (24 / 120 : ℝ) * h_phi

/-- $m_3 = 0$: No spin-3/2 invariants in $I^*$. -/
theorem m_three : m 3 = 0 := by
  rw [m, sum_chi_binaryIcosahedral 3]
  rw [chi_one 3, chi_centralInv 3]
  rw [chi_re_three_0, chi_re_three_half, chi_re_three_neg_half]
  rw [chi_re_three_phi_half, chi_re_three_neg_phi_half, chi_re_three_phi_inv_half, chi_re_three_neg_phi_inv_half]
  ring

/-- $m_4 = 0$: No spin-2 invariants in $I^*$. -/
theorem m_four : m 4 = 0 := by
  rw [m, sum_chi_binaryIcosahedral 4]
  rw [chi_one 4, chi_centralInv 4]
  rw [chi_re_four_0, chi_re_four_half, chi_re_four_neg_half]
  rw [chi_re_four_phi_half, chi_re_four_neg_phi_half, chi_re_four_phi_inv_half, chi_re_four_neg_phi_inv_half]
  ring

/-- $m_5 = 0$: No spin-5/2 invariants in $I^*$. -/
theorem m_five : m 5 = 0 := by
  rw [m, sum_chi_binaryIcosahedral 5]
  rw [chi_one 5, chi_centralInv 5]
  rw [chi_re_five_0, chi_re_five_half, chi_re_five_neg_half]
  rw [chi_re_five_phi_half, chi_re_five_neg_phi_half, chi_re_five_phi_inv_half, chi_re_five_neg_phi_inv_half]
  ring

/-- $m_6 = 0$: In the $\mathrm{SU}(2)$ representation of degree 6 (dimension 7), there are no $I^*$-invariants. -/
theorem m_six : m 6 = 0 := by
  rw [m, sum_chi_binaryIcosahedral 6]
  rw [chi_one 6, chi_centralInv 6]
  rw [chi_re_six_0, chi_re_six_half, chi_re_six_neg_half]
  rw [chi_re_six_phi_half, chi_re_six_neg_phi_half, chi_re_six_phi_inv_half, chi_re_six_neg_phi_inv_half]
  have h_phi := phi_sub_phi_inv
  linear_combination (-24 / 120 : ℝ) * h_phi

/-- $m_{12} = 1$: The first non-trivial icosahedral invariant in $\mathrm{SU}(2)$ occurs at degree 12
(dimension 13), corresponding to Klein's degree 6 icosahedral harmonic invariant on $S^2$. -/
theorem m_twelve : m 12 = 1 := by
  rw [m, sum_chi_binaryIcosahedral 12]
  rw [chi_one 12, chi_centralInv 12]
  rw [chi_re_twelve_0, chi_re_twelve_half, chi_re_twelve_neg_half]
  rw [chi_re_twelve_phi_half, chi_re_twelve_neg_phi_half, chi_re_twelve_phi_inv_half, chi_re_twelve_neg_phi_inv_half]
  have h_phi := phi_sub_phi_inv
  linear_combination (24 / 120 : ℝ) * h_phi

/-! ### $\mathrm{SO}(3)$ Invariant Multiplicities $m^{\mathrm{SO}(3)}_L$ -/

/-- Invariant subspace multiplicity for the $\mathrm{SO}(3)$ irreducible representation of degree $L$
(dimension $2L + 1$), corresponding to $\mathrm{SU}(2)$ degree $2L$. -/
def m_SO3 (L : ℕ) : ℝ := m (2 * L)

theorem m_SO3_zero : m_SO3 0 = 1 := m_zero

theorem m_SO3_one : m_SO3 1 = 0 := m_two

theorem m_SO3_two : m_SO3 2 = 0 := m_four

theorem m_SO3_three : m_SO3 3 = 0 := m_six

/-- Klein's icosahedral invariant: $m^{\mathrm{SO}(3)}_6 = 1$. The first non-trivial icosahedral
spherical harmonic on $S^2 \cong \mathrm{SO}(3)/\mathrm{SO}(2)$ occurs at multipole $L = 6$. -/
theorem m_SO3_six : m_SO3 6 = 1 := m_twelve

/-! ### Laplacian Eigenvalues and Heat Kernel Trace on $S^3 / I^*$ -/

/-- Eigenvalue $\lambda_\ell = \ell(\ell + 2)$ of the Laplace-Beltrami operator on $S^3$. -/
def laplacianEigenvalue (l : ℕ) : ℝ :=
  (l : ℝ) * ((l : ℝ) + 2)

lemma laplacianEigenvalue_zero : laplacianEigenvalue 0 = 0 := by
  simp [laplacianEigenvalue]

lemma laplacianEigenvalue_twelve : laplacianEigenvalue 12 = 168 := by
  simp [laplacianEigenvalue]
  norm_num

/-- Heat trace summand for degree $\ell$: $m_\ell (\ell + 1) e^{-t \ell(\ell + 2)}$. -/
def heatTraceTerm (t : ℝ) (l : ℕ) : ℝ :=
  m l * ((l : ℝ) + 1) * Real.exp (-t * laplacianEigenvalue l)

/-- Heat kernel trace on Poincaré Dodecahedral Space $S^3 / I^*$:
$$Z(t) = \sum_{\ell = 0}^\infty m_\ell (\ell + 1) e^{-t \ell (\ell + 2)}$$ -/
def heatTrace (t : ℝ) : ℝ :=
  ∑' l : ℕ, heatTraceTerm t l

lemma heatTraceTerm_zero (t : ℝ) : heatTraceTerm t 0 = 1 := by
  simp only [heatTraceTerm, m_zero, laplacianEigenvalue_zero]
  ring_nf
  exact Real.exp_zero

lemma heatTraceTerm_one (t : ℝ) : heatTraceTerm t 1 = 0 := by
  simp only [heatTraceTerm, m_one, MulZeroClass.zero_mul]

lemma heatTraceTerm_two (t : ℝ) : heatTraceTerm t 2 = 0 := by
  simp only [heatTraceTerm, m_two, MulZeroClass.zero_mul]

lemma heatTraceTerm_three (t : ℝ) : heatTraceTerm t 3 = 0 := by
  simp only [heatTraceTerm, m_three, MulZeroClass.zero_mul]

lemma heatTraceTerm_four (t : ℝ) : heatTraceTerm t 4 = 0 := by
  simp only [heatTraceTerm, m_four, MulZeroClass.zero_mul]

lemma heatTraceTerm_five (t : ℝ) : heatTraceTerm t 5 = 0 := by
  simp only [heatTraceTerm, m_five, MulZeroClass.zero_mul]

lemma heatTraceTerm_six (t : ℝ) : heatTraceTerm t 6 = 0 := by
  simp only [heatTraceTerm, m_six, MulZeroClass.zero_mul]

lemma heatTraceTerm_twelve (t : ℝ) :
    heatTraceTerm t 12 = 13 * Real.exp (-168 * t) := by
  simp only [heatTraceTerm, m_twelve, laplacianEigenvalue_twelve]
  ring_nf
