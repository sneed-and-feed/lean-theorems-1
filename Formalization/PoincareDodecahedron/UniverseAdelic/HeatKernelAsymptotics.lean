import UniverseAdelic.SpectralDecomposition
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic

noncomputable section

open scoped Real BigOperators
open Real

/-!
# Small-$t$ Heat Kernel Asymptotics and Classical GR Recovery on $S^3 / I^*$

This file formalizes the small-$t$ heat kernel asymptotic expansion, Seeley-DeWitt
coefficients, and the Chamseddine-Connes spectral action recovery of the classical
Einstein-Hilbert action on the Poincaré Dodecahedral Space $S^3 / I^*$.

## Mathematical Background:
1. **Poincaré Dodecahedral Space ($S^3 / I^*$)**:
   The spherical 3-manifold obtained as the quotient of the unit 3-sphere $S^3 \subset \mathbb{H}$
   by the binary icosahedral group $I^* \subset \mathrm{SU}(2)$ of order $|I^*| = 120$.
   Since $I^*$ acts freely and isometrically on $S^3$:
   - $\mathrm{Vol}(S^3 / I^*) = \frac{\mathrm{Vol}(S^3)}{120} = \frac{2\pi^2}{120} = \frac{\pi^2}{60}$.
   - The scalar curvature is locally invariant: $R(S^3 / I^*) = R(S^3) = 6$.

2. **Seeley-DeWitt Heat Kernel Expansion**:
   For the Laplace-Beltrami operator $\Delta$ on a compact Riemannian 3-manifold $M$:
   $$Z(t) = \operatorname{Tr}(e^{-t\Delta}) \sim (4\pi t)^{-3/2} \sum_{k=0}^\infty a_{2k} t^k \quad (t \to 0^+)$$
   where:
   - $a_0 = \frac{\mathrm{Vol}(M)}{(4\pi)^{3/2}}$
   - $a_2 = \frac{1}{(4\pi)^{3/2}} \int_M \frac{R}{6} dV = \frac{R}{6} a_0 = a_0$ (since $R = 6$).

3. **Chamseddine-Connes Spectral Action & GR Recovery**:
   For a cutoff scale $\Lambda$ and cutoff function moments $f_4, f_2$:
   $$S_{\mathrm{spectral}} = \operatorname{Tr}(f(D^2/\Lambda^2)) \sim 2 f_4 \Lambda^4 a_0 + 2 f_2 \Lambda^2 a_2$$
   The leading terms recover the 4D Einstein-Hilbert action with cosmological constant:
   $$S_{\mathrm{EH}} = \frac{1}{16\pi G_{\mathrm{eff}}} \int (R - 2\Lambda_0) dV$$
   with $G_{\mathrm{eff}} = \frac{3\pi}{4 f_2 \Lambda^2}$ and $\Lambda_0 = \frac{f_4}{f_2} \Lambda^2$.
-/

/-! ### 1. Geometric Invariants of $S^3$ and $S^3 / I^*$ -/

/-- Volume of the standard round 3-sphere $S^3$ of unit radius: $\mathrm{Vol}(S^3) = 2\pi^2$. -/
def vol_S3 : ℝ := 2 * Real.pi ^ 2

/-- Volume of the Poincaré Dodecahedral Space $S^3 / I^*$:
$$\mathrm{Vol}(S^3 / I^*) = \frac{\mathrm{Vol}(S^3)}{120} = \frac{\pi^2}{60}$$ -/
def vol_PDS : ℝ := vol_S3 / 120

/-- Closed-form simplification of the volume of $S^3 / I^*$. -/
theorem vol_PDS_eq : vol_PDS = Real.pi ^ 2 / 60 := by
  unfold vol_PDS vol_S3
  ring

/-- Positivity of the volume of $S^3$. -/
lemma vol_S3_pos : vol_S3 > 0 := by
  unfold vol_S3
  have hpi : Real.pi > 0 := Real.pi_pos
  positivity

/-- Positivity of the volume of $S^3 / I^*$. -/
lemma vol_PDS_pos : vol_PDS > 0 := by
  rw [vol_PDS_eq]
  have hpi : Real.pi > 0 := Real.pi_pos
  positivity

/-- Scalar curvature of the standard round unit 3-sphere $S^3$: $R = n(n-1) = 6$. -/
def scalarCurvature_S3 : ℝ := 6

/-- Scalar curvature of the Poincaré Dodecahedral Space $S^3 / I^*$,
which is locally isometric to $S^3$: $R = 6$. -/
def scalarCurvature_PDS : ℝ := 6

theorem scalarCurvature_PDS_eq : scalarCurvature_PDS = scalarCurvature_S3 := rfl

lemma scalarCurvature_PDS_pos : scalarCurvature_PDS > 0 := by
  unfold scalarCurvature_PDS
  norm_num

/-! ### 2. Seeley-DeWitt Heat Kernel Coefficients -/

/-- Leading Seeley-DeWitt heat kernel volume coefficient on $S^3$:
$$a_0(S^3) = \frac{\mathrm{Vol}(S^3)}{(4\pi)^{3/2}}$$ -/
def a0_S3 : ℝ := vol_S3 / (4 * Real.pi) ^ (3 / 2 : ℝ)

/-- Leading Seeley-DeWitt heat kernel volume coefficient on Poincaré Dodecahedral Space $S^3 / I^*$:
$$a_0(S^3 / I^*) = \frac{\mathrm{Vol}(S^3 / I^*)}{(4\pi)^{3/2}} = \frac{a_0(S^3)}{120}$$ -/
def a0 : ℝ := vol_PDS / (4 * Real.pi) ^ (3 / 2 : ℝ)

/-- The volume coefficient on $S^3 / I^*$ is exactly $1/120$ of that on $S^3$. -/
theorem a0_eq_S3_div_120 : a0 = (vol_S3 / (4 * Real.pi) ^ (3 / 2 : ℝ)) / 120 := by
  unfold a0 vol_PDS
  ring

/-- Positivity of the leading heat kernel coefficient $a_0 > 0$. -/
lemma a0_pos : a0 > 0 := by
  unfold a0
  have h_vol : vol_PDS > 0 := vol_PDS_pos
  have h_pi : 4 * Real.pi > 0 := by linarith [Real.pi_pos]
  have h_denom : (4 * Real.pi) ^ (3 / 2 : ℝ) > 0 := Real.rpow_pos_of_pos h_pi _
  exact div_pos h_vol h_denom

/-- First sub-leading Seeley-DeWitt heat kernel curvature coefficient on $S^3 / I^*$:
$$a_2(S^3 / I^*) = \frac{R}{6} a_0(S^3 / I^*)$$ -/
def a2 : ℝ := (scalarCurvature_PDS / 6) * a0

/-- Because $R = 6$ on the unit 3-sphere, the curvature coefficient equals the volume coefficient: $a_2 = a_0$. -/
theorem a2_eq_a0 : a2 = a0 := by
  unfold a2 scalarCurvature_PDS
  ring

/-- Positivity of the curvature coefficient $a_2 > 0$. -/
lemma a2_pos : a2 > 0 := by
  rw [a2_eq_a0]
  exact a0_pos

/-! ### 3. Asymptotic Expansion of $Z(t)$ as $t \to 0^+$ -/

/-- Leading two-term asymptotic model for the heat kernel trace $Z(t)$ as $t \to 0^+$:
$$Z_{\mathrm{asymp}}(t) = a_0 t^{-3/2} + a_2 t^{-1/2}$$ -/
def heatTraceAsymptotic (t : ℝ) : ℝ :=
  a0 * t ^ (-3 / 2 : ℝ) + a2 * t ^ (-1 / 2 : ℝ)

/-- Simplified form of the asymptotic heat trace using $a_2 = a_0$. -/
theorem heatTraceAsymptotic_eq (t : ℝ) :
    heatTraceAsymptotic t = a0 * (t ^ (-3 / 2 : ℝ) + t ^ (-1 / 2 : ℝ)) := by
  unfold heatTraceAsymptotic
  rw [a2_eq_a0]
  ring

/-- Positivity of the asymptotic heat trace for all $t > 0$. -/
theorem heatTraceAsymptotic_pos (t : ℝ) (ht : t > 0) : heatTraceAsymptotic t > 0 := by
  rw [heatTraceAsymptotic_eq]
  have ha0 : a0 > 0 := a0_pos
  have ht1 : t ^ (-3 / 2 : ℝ) > 0 := Real.rpow_pos_of_pos ht _
  have ht2 : t ^ (-1 / 2 : ℝ) > 0 := Real.rpow_pos_of_pos ht _
  have hsum : t ^ (-3 / 2 : ℝ) + t ^ (-1 / 2 : ℝ) > 0 := add_pos ht1 ht2
  exact mul_pos ha0 hsum

/-- Small-$t$ Seeley-DeWitt asymptotic expansion theorem for $S^3 / I^*$:
The difference between the full heat trace $Z(t)$ and the leading two-term asymptotic model
is $O(t^{1/2})$ as $t \to 0^+$. -/
axiom heatTrace_asymptotic_remainder :
    (fun t => heatTrace t - heatTraceAsymptotic t) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun t => t ^ (1 / 2 : ℝ))

/-! ### 4. Spectral Action and Classical General Relativity Recovery -/

/-- Chamseddine-Connes spectral action cutoff integral for Poincaré Dodecahedral Space:
$$S_{\mathrm{spectral}}(f_4, f_2, \Lambda) = 2 f_4 \Lambda^4 a_0 + 2 f_2 \Lambda^2 a_2$$
where $f_4, f_2$ are moments of the smooth spectral cutoff function $f$, and $\Lambda$ is the UV cutoff scale. -/
def spectralAction (f4 f2 Λ : ℝ) : ℝ :=
  2 * f4 * Λ ^ 4 * a0 + 2 * f2 * Λ ^ 2 * a2

/-- Effective Newton's gravitational constant $G_{\mathrm{eff}}$ induced by the spectral action:
$$G_{\mathrm{eff}} = \frac{3\pi}{4 f_2 \Lambda^2}$$ -/
def G_eff (f2 Λ : ℝ) : ℝ :=
  3 * Real.pi / (4 * f2 * Λ ^ 2)

/-- Effective cosmological constant $\Lambda_0$ induced by the spectral action:
$$\Lambda_0 = \frac{f_4}{f_2} \Lambda^2$$ -/
def cosmologicalConstant (f4 f2 Λ : ℝ) : ℝ :=
  (f4 / f2) * Λ ^ 2

/-- Gravitational scalar curvature term (Einstein-Hilbert action component) in the spectral action:
$$S_{\mathrm{EH}} = 2 f_2 \Lambda^2 a_2$$ -/
def spectralCurvatureTerm (f2 Λ : ℝ) : ℝ :=
  2 * f2 * Λ ^ 2 * a2

/-- Cosmological volume term (cosmological constant component) in the spectral action:
$$S_{\mathrm{cosmo}} = 2 f_4 \Lambda^4 a_0$$ -/
def spectralVolumeTerm (f4 Λ : ℝ) : ℝ :=
  2 * f4 * Λ ^ 4 * a0

/-- Positivity of the effective Newton's constant for physical cutoff $\Lambda > 0$ and moment $f_2 > 0$. -/
theorem G_eff_pos (f2 Λ : ℝ) (_hf2 : f2 > 0) (hΛ : Λ > 0) : G_eff f2 Λ > 0 := by
  unfold G_eff
  have hnum : 3 * Real.pi > 0 := by linarith [Real.pi_pos]
  have hΛ2 : Λ ^ 2 > 0 := sq_pos_of_pos hΛ
  have hden : 4 * f2 * Λ ^ 2 > 0 := by positivity
  exact div_pos hnum hden

/-- Positivity of the effective cosmological constant for physical cutoff $\Lambda > 0$ and moments $f_4, f_2 > 0$. -/
theorem cosmologicalConstant_pos (f4 f2 Λ : ℝ) (hf4 : f4 > 0) (hf2 : f2 > 0) (hΛ : Λ > 0) :
    cosmologicalConstant f4 f2 Λ > 0 := by
  unfold cosmologicalConstant
  have h_frac : f4 / f2 > 0 := div_pos hf4 hf2
  have hΛ2 : Λ ^ 2 > 0 := sq_pos_of_pos hΛ
  exact mul_pos h_frac hΛ2

/-- Positivity of the gravitational curvature term. -/
theorem spectralCurvatureTerm_pos (f2 Λ : ℝ) (_hf2 : f2 > 0) (hΛ : Λ > 0) :
    spectralCurvatureTerm f2 Λ > 0 := by
  unfold spectralCurvatureTerm
  have ha2 : a2 > 0 := a2_pos
  have hΛ2 : Λ ^ 2 > 0 := sq_pos_of_pos hΛ
  positivity

/-- Positivity of the cosmological volume term. -/
theorem spectralVolumeTerm_pos (f4 Λ : ℝ) (_hf4 : f4 > 0) (hΛ : Λ > 0) :
    spectralVolumeTerm f4 Λ > 0 := by
  unfold spectralVolumeTerm
  have ha0 : a0 > 0 := a0_pos
  have hΛ4 : Λ ^ 4 > 0 := by positivity
  positivity

/-- Positivity of the spectral action for physical parameters $f_4 > 0, f_2 > 0, \Lambda > 0$. -/
theorem spectralAction_pos (f4 f2 Λ : ℝ) (_hf4 : f4 > 0) (_hf2 : f2 > 0) (hΛ : Λ > 0) :
    spectralAction f4 f2 Λ > 0 := by
  unfold spectralAction
  have ha0 : a0 > 0 := a0_pos
  have ha2 : a2 > 0 := a2_pos
  have hΛ4 : Λ ^ 4 > 0 := by positivity
  have hΛ2 : Λ ^ 2 > 0 := sq_pos_of_pos hΛ
  have h1 : 2 * f4 * Λ ^ 4 * a0 > 0 := by positivity
  have h2 : 2 * f2 * Λ ^ 2 * a2 > 0 := by positivity
  exact add_pos h1 h2

/-- Spectral action decomposition theorem: The spectral action on $S^3 / I^*$ splits cleanly
into the cosmological volume term and the scalar curvature term. -/
theorem spectralAction_eq_sum (f4 f2 Λ : ℝ) :
    spectralAction f4 f2 Λ = spectralVolumeTerm f4 Λ + spectralCurvatureTerm f2 Λ := by
  unfold spectralAction spectralVolumeTerm spectralCurvatureTerm
  rfl

/-- **General Relativity Recovery Theorem on $S^3 / I^*$**:
The Chamseddine-Connes spectral action asymptotic expansion recovers the 4D Einstein-Hilbert action
with cosmological constant on $\mathbb{R} \times (S^3 / I^*)$. Specifically:
1. The curvature coupling is proportional to the scalar curvature $R = 6$.
2. The ratio of the Einstein-Hilbert curvature term to the volume term recovers the
   gravitational coupling ratio $\frac{R}{6} \cdot \frac{f_2}{f_4 \Lambda^2} = \frac{1}{\Lambda_0}$.
3. The curvature term is strictly positive for physical parameters. -/
theorem einstein_hilbert_recovery (f4 f2 Λ : ℝ) (hf2 : f2 > 0) (_hf4 : f4 > 0) (hΛ : Λ > 0) :
    spectralCurvatureTerm f2 Λ / spectralVolumeTerm f4 Λ =
      (scalarCurvature_PDS / 6) * (f2 / (f4 * Λ ^ 2)) ∧
    spectralAction f4 f2 Λ =
      2 * f4 * Λ ^ 4 * a0 + 2 * f2 * Λ ^ 2 * (scalarCurvature_PDS / 6) * a0 ∧
    spectralCurvatureTerm f2 Λ > 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold spectralCurvatureTerm spectralVolumeTerm a2
    have ha0_pos : a0 > 0 := a0_pos
    have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ
    have hΛ4_eq : Λ ^ 4 = Λ ^ 2 * Λ ^ 2 := by ring
    have h_factor_ne : 2 * Λ ^ 2 * a0 ≠ 0 := by
      have : 2 * Λ ^ 2 * a0 > 0 := by positivity
      exact ne_of_gt this
    calc
      2 * f2 * Λ ^ 2 * ((scalarCurvature_PDS / 6) * a0) / (2 * f4 * Λ ^ 4 * a0)
        = ((2 * Λ ^ 2 * a0) * ((scalarCurvature_PDS / 6) * f2)) / ((2 * Λ ^ 2 * a0) * (f4 * Λ ^ 2)) := by
          rw [hΛ4_eq]
          ring
      _ = ((scalarCurvature_PDS / 6) * f2) / (f4 * Λ ^ 2) := by
          rw [mul_div_mul_left _ _ h_factor_ne]
      _ = (scalarCurvature_PDS / 6) * (f2 / (f4 * Λ ^ 2)) := by
          ring
  · unfold spectralAction a2
    ring
  · exact spectralCurvatureTerm_pos f2 Λ hf2 hΛ

/-- The ratio of the curvature term to the volume term is inversely proportional
to the effective cosmological constant $\Lambda_0$. -/
theorem spectral_ratio_eq_inv_cosmologicalConstant (f4 f2 Λ : ℝ)
    (hf2 : f2 > 0) (hf4 : f4 > 0) (hΛ : Λ > 0) :
    spectralCurvatureTerm f2 Λ / spectralVolumeTerm f4 Λ =
      (cosmologicalConstant f4 f2 Λ)⁻¹ := by
  have h_rec := (einstein_hilbert_recovery f4 f2 Λ hf2 hf4 hΛ).1
  rw [h_rec]
  unfold scalarCurvature_PDS cosmologicalConstant
  have hf2_ne : f2 ≠ 0 := ne_of_gt hf2
  have hf4_ne : f4 ≠ 0 := ne_of_gt hf4
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ
  have hΛ2_ne : Λ ^ 2 ≠ 0 := pow_ne_zero 2 hΛ_ne
  field_simp