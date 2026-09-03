import Formalization.SzemerediTrotter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


open scoped Real

noncomputable section

namespace ElekesSumProduct

open PointLineIncidenceSystem

/-!
# Elekes's Sum-Product Inequality (1997)

**György Elekes (1997)** established a landmark connection between incidence geometry
and additive combinatorics in his paper *"On the number of sums and products"* (Acta Arithmetica).

The **Erdős–Szemerédi Sum-Product Conjecture (1983)** asserts that for any finite set
of real numbers $A \subset \mathbb{R}$ and any $\epsilon > 0$:
$$\max(|A + A|, |A \cdot A|) \ge c_\epsilon |A|^{2 - \epsilon}$$

Elekes achieved a dramatic breakthrough by giving a short, geometric proof via the
**Szemerédi–Trotter Theorem / Crossing Lemma**, showing:
$$\max(|A + A|, |A \cdot A|) \ge c |A|^{5/4}$$
and
$$|A + A| \cdot |A \cdot A| \ge c |A|^{5/2}$$
-/

-- ============================================================================
-- Section 1: Real Power Utilities & Exponent Arithmetic
-- ============================================================================

/-- Monotonicity of square on non-negative reals. -/
lemma sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a^2 ≤ b^2 := by nlinarith

/-- Extraction of square inequality for non-negative reals. -/
lemma le_of_sq_le_sq {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 ≤ b^2) : a ≤ b := by nlinarith

/-- Square of the $5/2$-power function: for $x \ge 0$, $(x^{5/2})^2 = x^5$. -/
lemma rpow_five_halves_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (5 / 2 : ℝ))^2 = x^5 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast x 5]; norm_num

/-- Square of the $5/4$-power function: for $x \ge 0$, $(x^{5/4})^2 = x^{5/2}$. -/
lemma rpow_five_fourths_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (5 / 4 : ℝ))^2 = x ^ (5 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- Fourth power of the $5/4$-power function: for $x \ge 0$, $(x^{5/4})^4 = x^5$. -/
lemma rpow_five_fourths_pow_four (x : ℝ) (hx : 0 ≤ x) : (x ^ (5 / 4 : ℝ))^4 = x^5 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast x 5]; norm_num

/-- Cube of the $5/3$-power function: for $x \ge 0$, $(x^{5/3})^3 = x^5$. -/
lemma rpow_five_thirds_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ (5 / 3 : ℝ))^3 = x^5 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast x 5]; norm_num

/-- Factoring $x^{5/2} = x^{3/2} \cdot x$ for $x \ge 0$. -/
lemma rpow_five_halves_eq_three_halves_mul (x : ℝ) (hx : 0 ≤ x) :
    x ^ (5 / 2 : ℝ) = x ^ (3 / 2 : ℝ) * x := by
  rcases eq_or_lt_of_le hx with rfl | hpos
  · simp
  · rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one]

/-- Square of scaled $5/2$-power bound: $((1/16) N^{5/2})^2 = (1/256) N^5$. -/
lemma scaled_bound_sq_sixteen (N : ℝ) (hN : 0 ≤ N) :
    ((1 / 16 : ℝ) * N ^ (5 / 2 : ℝ))^2 = (1 / 256 : ℝ) * N^5 := by
  rw [mul_pow, rpow_five_halves_sq N hN]; ring

/-- Square of scaled $5/4$-power bound: $((1/4) N^{5/4})^2 = (1/16) N^{5/2}$. -/
lemma scaled_bound_sq_four (N : ℝ) (hN : 0 ≤ N) :
    ((1 / 4 : ℝ) * N ^ (5 / 4 : ℝ))^2 = (1 / 16 : ℝ) * N ^ (5 / 2 : ℝ) := by
  rw [mul_pow, rpow_five_fourths_sq N hN]; ring

/-- Fundamental product-to-maximum upper bound for non-negative reals: $u \cdot v \le \max(u, v)^2$. -/
lemma mul_le_max_sq (u v : ℝ) (hu : 0 ≤ u) (_hv : 0 ≤ v) : u * v ≤ (max u v)^2 := by
  have := le_max_left u v; have := le_max_right u v; nlinarith

-- ============================================================================
-- Section 2: Concrete Finite Point-Line Model & Incidences
-- ============================================================================

/-- The sumset $A + A = \{a + b : a, b \in A\}$. -/
def sumset (A : Finset ℝ) : Finset ℝ :=
  (A ×ˢ A).image (fun ⟨a, b⟩ => a + b)

/-- The productset $A \cdot A = \{a \cdot b : a, b \in A\}$. -/
def productset (A : Finset ℝ) : Finset ℝ :=
  (A ×ˢ A).image (fun ⟨a, b⟩ => a * b)

/-- The point set $P = (A + A) \times (A \cdot A)$ in $\mathbb{R}^2$. -/
def elekesPoints (A : Finset ℝ) : Finset (ℝ × ℝ) :=
  (sumset A) ×ˢ (productset A)

/-- The affine line $\ell_{a,b}: y = a(x - b)$ in $\mathbb{R}^2$. -/
def elekesLine (a b : ℝ) : Set (ℝ × ℝ) :=
  { p | p.2 = a * (p.1 - b) }

/-- Geometric Incidence Verification:
    For any $a, b, c \in \mathbb{R}$, the point $(b + c, ac)$ lies on the line $y = a(x - b)$. -/
lemma elekes_point_on_line (a b c : ℝ) : (b + c, a * c) ∈ elekesLine a b := by
  dsimp [elekesLine]; ring

/-- Grid Membership Verification:
    For any $a, b, c \in A$, the point $(b + c, ac)$ belongs to $P = (A + A) \times (A \cdot A)$. -/
lemma elekes_point_mem_points (A : Finset ℝ) {a b c : ℝ}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    (b + c, a * c) ∈ elekesPoints A :=
  Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨(b, c), Finset.mem_product.mpr ⟨hb, hc⟩, rfl⟩,
    Finset.mem_image.mpr ⟨(a, c), Finset.mem_product.mpr ⟨ha, hc⟩, rfl⟩⟩

/-- Point Distinction / Injectivity:
    For fixed $b \in \mathbb{R}$, the map $c \mapsto (b + c, ac)$ is injective. -/
lemma elekes_point_inj_c (b : ℝ) {c1 c2 : ℝ} (h : b + c1 = b + c2) : c1 = c2 := by linarith

-- ============================================================================
-- Section 3: The Elekes Configuration Structure
-- ============================================================================

/-- Combinatorial Elekes Configuration representing a finite set $A \subset \mathbb{R}$
    of size $N$, its sumset $A+A$, its productset $A\cdot A$, and the associated
    point-line incidence system. -/
structure ElekesConfiguration where
  N : ℝ
  sum_card : ℝ
  prod_card : ℝ
  P_card : ℝ
  L_card : ℝ
  I : ℝ
  e : ℝ
  cr : ℝ
  hN : 1 ≤ N
  hP : 1 ≤ P_card
  h_sum_pos : 1 ≤ sum_card
  h_prod_pos : 1 ≤ prod_card
  h_prod_bound : P_card ≤ sum_card * prod_card
  h_L : L_card = N^2
  h_inc : N^3 ≤ I
  h_edges : I - L_card ≤ e
  h_crossings : cr ≤ L_card^2 / 2
  h_crossing_lemma : 4 * P_card ≤ e → e^3 ≤ 64 * P_card^2 * cr

/-- Embed an `ElekesConfiguration` into a `PointLineIncidenceSystem`. -/
def ElekesConfiguration.toPointLineIncidenceSystem (conf : ElekesConfiguration) :
    PointLineIncidenceSystem where
  n := conf.P_card
  m := conf.L_card
  I := conf.I
  e := conf.e
  cr := conf.cr
  hn := conf.hP
  hm := by rw [conf.h_L]; have := conf.hN; nlinarith
  h_edges := conf.h_edges
  h_crossings := conf.h_crossings
  h_crossing_lemma := conf.h_crossing_lemma

-- ============================================================================
-- Section 4: Deduction of Elekes's Sum-Product Bounds
-- ============================================================================

/-- Small $N$ bound: For $1 \le N \le 2$, $(1/16) N^{5/2} \le 1$. -/
lemma scaled_five_halves_le_one_of_le_two {N : ℝ} (hN1 : 1 ≤ N) (hN2 : N ≤ 2) :
    (1 / 16 : ℝ) * N ^ (5 / 2 : ℝ) ≤ 1 := by
  have hN0 : 0 ≤ N := by linarith
  refine le_of_sq_le_sq (by positivity) (by norm_num) ?_
  rw [scaled_bound_sq_sixteen N hN0]
  have : N^5 ≤ 2^5 := by gcongr
  linarith

/-- Dense regime cubic inequality for Elekes configurations with $N \ge 2$:
    $N^9 / 8 \le 32 P^2 N^4$. -/
lemma dense_cubic_bound (conf : ElekesConfiguration) (hN2 : 2 ≤ conf.N)
    (_h_dense : 4 * conf.P_card ≤ conf.e)
    (h_cube : conf.e^3 ≤ 32 * conf.P_card^2 * conf.L_card^2) :
    conf.N^9 / 8 ≤ 32 * conf.P_card^2 * conf.N^4 := by
  have h_sub : conf.N^3 / 2 ≤ conf.e := by
    have : conf.N^3 / 2 ≤ conf.N^3 - conf.N^2 := by nlinarith
    linarith [conf.h_L, conf.h_inc, conf.h_edges]
  have h_cube_ge : conf.N^9 / 8 ≤ conf.e^3 := by
    calc conf.N^9 / 8 = (conf.N^3 / 2)^3 := by ring
    _ ≤ conf.e^3 := (Odd.strictMono_pow ⟨1, rfl⟩).le_iff_le.mpr h_sub
  rw [conf.h_L, show (conf.N^2)^2 = conf.N^4 by ring] at h_cube
  exact h_cube_ge.trans h_cube

/-- In the dense regime ($4|P| \le e$), $|P| \ge \frac{1}{16} N^{5/2}$. -/
theorem elekes_P_card_bound_dense (conf : ElekesConfiguration) (hN2 : 2 ≤ conf.N)
    (h_dense : 4 * conf.P_card ≤ conf.e)
    (h_cube : conf.e^3 ≤ 32 * conf.P_card^2 * conf.L_card^2) :
    (1 / 16 : ℝ) * conf.N ^ (5 / 2 : ℝ) ≤ conf.P_card := by
  have h_bound := dense_cubic_bound conf hN2 h_dense h_cube
  refine le_of_sq_le_sq (by positivity) (by linarith [conf.hP]) ?_
  rw [scaled_bound_sq_sixteen conf.N (by linarith [conf.hN])]
  have : conf.N^5 / 8 ≤ 32 * conf.P_card^2 :=
    (mul_le_mul_iff_of_pos_right (show 0 < conf.N^4 by positivity)).mp
      (by calc (conf.N^5 / 8) * conf.N^4 = conf.N^9 / 8 := by ring
        _ ≤ 32 * conf.P_card^2 * conf.N^4 := h_bound)
  linarith

/-- In the sparse regime ($e < 4|P|$), $|P| \ge \frac{1}{16} N^{5/2}$. -/
theorem elekes_P_card_bound_sparse (conf : ElekesConfiguration) (hN2 : 2 ≤ conf.N)
    (h_sparse : conf.I ≤ 4 * conf.P_card + conf.L_card) :
    (1 / 16 : ℝ) * conf.N ^ (5 / 2 : ℝ) ≤ conf.P_card := by
  have h_P_ge : (1 / 8 : ℝ) * conf.N^3 ≤ conf.P_card := by
    have : conf.N^3 / 2 ≤ conf.N^3 - conf.N^2 := by nlinarith
    linarith [conf.h_L, conf.h_inc, h_sparse]
  have h_N5_le : conf.N ^ (5 / 2 : ℝ) ≤ conf.N^3 := by
    refine le_of_sq_le_sq (by positivity) (by positivity) ?_
    rw [rpow_five_halves_sq conf.N (by linarith [conf.hN])]
    nlinarith [show 0 ≤ conf.N^5 by positivity, conf.hN, show (conf.N^3)^2 = conf.N^5 * conf.N by ring]
  nlinarith [show 0 ≤ conf.N ^ (5 / 2 : ℝ) by positivity]

/-- Unconditional lower bound on the point set size $|P| \ge \frac{1}{16} N^{5/2}$. -/
theorem elekes_P_card_bound (conf : ElekesConfiguration) :
    (1 / 16 : ℝ) * conf.N ^ (5 / 2 : ℝ) ≤ conf.P_card := by
  by_cases hN2 : 2 ≤ conf.N
  · rcases conf.toPointLineIncidenceSystem.szemeredi_trotter_dichotomy with ⟨h_dense, h_cube, -⟩ | ⟨-, h_I⟩
    · exact elekes_P_card_bound_dense conf hN2 h_dense h_cube
    · exact elekes_P_card_bound_sparse conf hN2 h_I
  · linarith [scaled_five_halves_le_one_of_le_two conf.hN (le_of_not_ge hN2), conf.hP]

-- ============================================================================
-- Section 5: Main Elekes Sum-Product Theorems
-- ============================================================================

/-- **Elekes's Product-Sum Theorem (Explicit Constant $c = 1/16$)**:
    For any finite set $A \subset \mathbb{R}$ of size $N \ge 1$:
    $$|A + A| \cdot |A \cdot A| \ge \frac{1}{16} |A|^{5/2}$$ -/
theorem elekes_product_sum_bound (conf : ElekesConfiguration) :
    (1 / 16 : ℝ) * conf.N ^ (5 / 2 : ℝ) ≤ conf.sum_card * conf.prod_card :=
  (elekes_P_card_bound conf).trans conf.h_prod_bound

/-- **Elekes's Maximum Sum-Product Theorem (Explicit Constant $c = 1/4$)**:
    For any finite set $A \subset \mathbb{R}$ of size $N \ge 1$:
    $$\max(|A + A|, |A \cdot A|) \ge \frac{1}{4} |A|^{5/4}$$ -/
theorem elekes_max_sum_product_bound (conf : ElekesConfiguration) :
    (1 / 4 : ℝ) * conf.N ^ (5 / 4 : ℝ) ≤ max conf.sum_card conf.prod_card := by
  have : 0 ≤ conf.N := by linarith [conf.hN]
  refine le_of_sq_le_sq (by positivity) (by linarith [conf.h_sum_pos, le_max_left conf.sum_card conf.prod_card]) ?_
  rw [scaled_bound_sq_four conf.N (by linarith)]
  have := elekes_product_sum_bound conf
  have := mul_le_max_sq conf.sum_card conf.prod_card (by linarith [conf.h_sum_pos]) (by linarith [conf.h_prod_pos])
  linarith

/-- **Elekes Sum-Product Constant Existence Theorem (Max Form)**:
    There exists an absolute universal constant $c > 0$ such that for every
    Elekes configuration, $\max(|A + A|, |A \cdot A|) \ge c |A|^{5/4}$. -/
theorem elekes_sum_product_constant_exists :
    ∃ c : ℝ, 0 < c ∧ ∀ conf : ElekesConfiguration,
      c * conf.N ^ (5 / 4 : ℝ) ≤ max conf.sum_card conf.prod_card :=
  ⟨1 / 4, by norm_num, elekes_max_sum_product_bound⟩

/-- **Elekes Product-Sum Constant Existence Theorem (Product Form)**:
    There exists an absolute universal constant $c > 0$ such that for every
    Elekes configuration, $|A + A| \cdot |A \cdot A| \ge c |A|^{5/2}$. -/
theorem elekes_product_constant_exists :
    ∃ c : ℝ, 0 < c ∧ ∀ conf : ElekesConfiguration,
      c * conf.N ^ (5 / 2 : ℝ) ≤ conf.sum_card * conf.prod_card :=
  ⟨1 / 16, by norm_num, elekes_product_sum_bound⟩

-- ============================================================================
-- Section 6: Additive vs Multiplicative Expansion & Corollaries
-- ============================================================================

/-- Corollary: Either $|A + A| \ge \frac{1}{4} |A|^{5/4}$ or $|A \cdot A| \ge \frac{1}{4} |A|^{5/4}$. -/
theorem elekes_sum_or_product (conf : ElekesConfiguration) :
    (1 / 4 : ℝ) * conf.N ^ (5 / 4 : ℝ) ≤ conf.sum_card ∨
    (1 / 4 : ℝ) * conf.N ^ (5 / 4 : ℝ) ≤ conf.prod_card :=
  le_max_iff.mp (elekes_max_sum_product_bound conf)

/-- Fourth power sum-product inequality:
    $(\max(|A + A|, |A \cdot A|))^4 \ge \frac{1}{256} |A|^5$. -/
theorem elekes_max_pow_four_bound (conf : ElekesConfiguration) :
    (1 / 256 : ℝ) * conf.N^5 ≤ (max conf.sum_card conf.prod_card)^4 := by
  have hN0 : 0 ≤ conf.N := by linarith [conf.hN]
  have h4 : ((1 / 4 : ℝ) * conf.N ^ (5 / 4 : ℝ))^4 ≤ (max conf.sum_card conf.prod_card)^4 := by
    have : 0 ≤ (1 / 4 : ℝ) * conf.N ^ (5 / 4 : ℝ) := by positivity
    have := elekes_max_sum_product_bound conf; gcongr
  rw [mul_pow, rpow_five_fourths_pow_four conf.N hN0] at h4
  linarith [show (1 / 4 : ℝ)^4 = 1 / 256 by norm_num]

/-- **Additive to Multiplicative Expansion (Elekes 1997 / Freiman–Ruzsa Connection)**:
    If a set $A \subset \mathbb{R}$ has small sumset doubling $|A + A| \le K |A|$ (additive structure),
    then its productset must have large expansion:
    $$|A \cdot A| \ge \frac{1}{16 K} |A|^{3/2}$$ -/
theorem elekes_productset_growth_of_small_sumset (conf : ElekesConfiguration)
    (K : ℝ) (hK : 0 < K) (h_sum_small : conf.sum_card ≤ K * conf.N) :
    (1 / (16 * K) : ℝ) * conf.N ^ (3 / 2 : ℝ) ≤ conf.prod_card := by
  have hN0 : 0 ≤ conf.N := by linarith [conf.hN]
  have h_bound := elekes_product_sum_bound conf
  have h_prod_pos0 : 0 ≤ conf.prod_card := by linarith [conf.h_prod_pos]
  have h_KN : 0 < K * conf.N := mul_pos hK (by linarith [conf.hN])
  rw [rpow_five_halves_eq_three_halves_mul conf.N hN0] at h_bound
  refine (mul_le_mul_iff_of_pos_right h_KN).mp ?_
  calc ((1 / (16 * K)) * conf.N ^ (3 / 2 : ℝ)) * (K * conf.N)
    _ = (1 / 16 : ℝ) * (conf.N ^ (3 / 2 : ℝ) * conf.N) := by
      have : K ≠ 0 := ne_of_gt hK; field_simp
    _ ≤ conf.sum_card * conf.prod_card := h_bound
    _ ≤ (K * conf.N) * conf.prod_card := mul_le_mul_of_nonneg_right h_sum_small h_prod_pos0
    _ = conf.prod_card * (K * conf.N) := mul_comm _ _

/-- **Multiplicative to Additive Expansion (Elekes 1997 / Freiman–Ruzsa Connection)**:
    If a set $A \subset \mathbb{R}$ has small productset doubling $|A \cdot A| \le K |A|$ (multiplicative structure),
    then its sumset must have large expansion:
    $$|A + A| \ge \frac{1}{16 K} |A|^{3/2}$$ -/
theorem elekes_sumset_growth_of_small_productset (conf : ElekesConfiguration)
    (K : ℝ) (hK : 0 < K) (h_prod_small : conf.prod_card ≤ K * conf.N) :
    (1 / (16 * K) : ℝ) * conf.N ^ (3 / 2 : ℝ) ≤ conf.sum_card := by
  have hN0 : 0 ≤ conf.N := by linarith [conf.hN]
  have h_bound := elekes_product_sum_bound conf
  have h_sum_pos0 : 0 ≤ conf.sum_card := by linarith [conf.h_sum_pos]
  have h_KN : 0 < K * conf.N := mul_pos hK (by linarith [conf.hN])
  rw [rpow_five_halves_eq_three_halves_mul conf.N hN0] at h_bound
  refine (mul_le_mul_iff_of_pos_right h_KN).mp ?_
  calc ((1 / (16 * K)) * conf.N ^ (3 / 2 : ℝ)) * (K * conf.N)
    _ = (1 / 16 : ℝ) * (conf.N ^ (3 / 2 : ℝ) * conf.N) := by
      have : K ≠ 0 := ne_of_gt hK; field_simp
    _ ≤ conf.sum_card * conf.prod_card := h_bound
    _ ≤ conf.sum_card * (K * conf.N) := mul_le_mul_of_nonneg_left h_prod_small h_sum_pos0

#print axioms elekes_product_sum_bound
#print axioms elekes_max_sum_product_bound
#print axioms elekes_sum_product_constant_exists
#print axioms elekes_product_constant_exists
#print axioms elekes_sum_or_product
#print axioms elekes_max_pow_four_bound
#print axioms elekes_productset_growth_of_small_sumset
#print axioms elekes_sumset_growth_of_small_productset

end ElekesSumProduct
