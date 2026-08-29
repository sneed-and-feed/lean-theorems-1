import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

noncomputable section

open scoped Quaternion Classical

open Real

/-- The Golden Ratio $\phi = (1+\sqrt{5})/2$. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2
scoped notation "φ" => phi

/-- Square of $\sqrt{5}$ is 5. -/
theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- Fundamental golden ratio identity: $\phi^2 = \phi + 1$. -/
theorem phi_sq : φ ^ 2 = φ + 1 := by
  dsimp [phi]
  have h5 : (Real.sqrt 5) ^ 2 = 5 := sqrt_five_sq
  nlinarith

/-- Fundamental golden ratio inverse identity: $\phi^{-1} = \phi - 1$. -/
theorem phi_inv : φ⁻¹ = φ - 1 := by
  have h_ne : φ ≠ 0 := by
    dsimp [phi]
    have : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have h_sq : φ * (φ - 1) = 1 := by
    calc φ * (φ - 1) = φ ^ 2 - φ := by ring
    _ = (φ + 1) - φ := by rw [phi_sq]
    _ = 1 := by ring
  exact (eq_inv_of_mul_eq_one_right h_sq).symm

/-- Helper constructor for quaternions in ℍ[ℝ]. -/
@[inline] def q (a b c d : ℝ) : ℍ[ℝ] := ⟨a, b, c, d⟩

/-- Golden ratio norm square identity: (φ⁻¹/2)² + (1/2)² + (φ/2)² = 1. -/
theorem golden_ratio_norm_sq_sum : (φ⁻¹ / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + (φ / 2) ^ 2 = 1 := by
  have h_phi_sq : φ ^ 2 = φ + 1 := phi_sq
  have h_inv : φ⁻¹ = φ - 1 := phi_inv
  have h_inv_sq : (φ⁻¹) ^ 2 = 2 - φ := by
    rw [h_inv]
    calc (φ - 1) ^ 2 = φ ^ 2 - 2 * φ + 1 := by ring
    _ = (φ + 1) - 2 * φ + 1 := by rw [h_phi_sq]
    _ = 2 - φ := by ring
  calc (φ⁻¹ / 2) ^ 2 + (1 / 2 : ℝ) ^ 2 + (φ / 2) ^ 2
    _ = (φ⁻¹) ^ 2 / 4 + 1 / 4 + φ ^ 2 / 4 := by ring
    _ = (2 - φ) / 4 + 1 / 4 + (φ + 1) / 4 := by rw [h_inv_sq, h_phi_sq]
    _ = 1 := by ring

/-- The 8 Lipschitz units: ±1, ±i, ±j, ±k. -/
def lipschitzUnits : Finset ℍ[ℝ] :=
  { q 1 0 0 0, q (-1) 0 0 0,
    q 0 1 0 0, q 0 (-1) 0 0,
    q 0 0 1 0, q 0 0 (-1) 0,
    q 0 0 0 1, q 0 0 0 (-1) }

/-- The 16 Hurwitz units: (±1/2, ±1/2, ±1/2, ±1/2). -/
def hurwitzUnits : Finset ℍ[ℝ] :=
  (Finset.univ : Finset (Bool × Bool × Bool × Bool)).image fun ⟨s0, s1, s2, s3⟩ =>
    let f (b : Bool) : ℝ := if b then (1 / 2) else (-1 / 2)
    q (f s0) (f s1) (f s2) (f s3)

/-- The 24 binary tetrahedral units (Lipschitz + Hurwitz units). -/
def binaryTetrahedralUnits : Finset ℍ[ℝ] :=
  lipschitzUnits ∪ hurwitzUnits

/-- The 12 even coordinate permutations of (0, a, b, c) in ℍ[ℝ]. -/
def evenPermutations (a b c : ℝ) : Finset ℍ[ℝ] :=
  { -- 0 at position 0
    q 0 a b c, q 0 b c a, q 0 c a b,
    -- 0 at position 1
    q a 0 c b, q b 0 a c, q c 0 b a,
    -- 0 at position 2
    q b c 0 a, q a b 0 c, q c a 0 b,
    -- 0 at position 3
    q c b a 0, q a c b 0, q b a c 0 }

/-- The 96 icosahedral units: all even permutations of (0, ±φ⁻¹/2, ±1/2, ±φ/2). -/
def icosahedralUnits : Finset ℍ[ℝ] :=
  (Finset.univ : Finset (Bool × Bool × Bool)).biUnion fun ⟨s0, s1, s2⟩ =>
    let a := if s0 then φ⁻¹ / 2 else -φ⁻¹ / 2
    let b := if s1 then 1 / 2 else -1 / 2
    let c := if s2 then φ / 2 else -φ / 2
    evenPermutations a b c

/-- The 120 elements of the binary icosahedral group in ℍ[ℝ]. -/
def binaryIcosahedralUnits : Finset ℍ[ℝ] :=
  binaryTetrahedralUnits ∪ icosahedralUnits

lemma normSq_q (a b c d : ℝ) : Quaternion.normSq (q a b c d) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  rw [Quaternion.normSq_def']
  rfl

lemma lipschitzUnits_normSq {u : ℍ[ℝ]} (h : u ∈ lipschitzUnits) : Quaternion.normSq u = 1 := by
  simp only [lipschitzUnits, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { rw [normSq_q]; ring }

lemma ite_sign_sq (s : Bool) (x : ℝ) : (if (s = true) then x else -x) ^ 2 = x ^ 2 := by
  cases s <;> simp

lemma hurwitzUnits_normSq {u : ℍ[ℝ]} (h : u ∈ hurwitzUnits) : Quaternion.normSq u = 1 := by
  simp only [hurwitzUnits, Finset.mem_image, Finset.mem_univ, true_and] at h
  rcases h with ⟨⟨s0, s1, s2, s3⟩, rfl⟩
  dsimp only
  rw [normSq_q]
  cases s0 <;> cases s1 <;> cases s2 <;> cases s3 <;> { dsimp; ring }

lemma evenPermutations_normSq (a b c : ℝ) {u : ℍ[ℝ]} (h : u ∈ evenPermutations a b c) :
    Quaternion.normSq u = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp only [evenPermutations, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    { rw [normSq_q]; ring }

lemma icosahedralUnits_normSq {u : ℍ[ℝ]} (h : u ∈ icosahedralUnits) : Quaternion.normSq u = 1 := by
  simp only [icosahedralUnits, Finset.mem_biUnion, Finset.mem_univ, true_and] at h
  rcases h with ⟨⟨s0, s1, s2⟩, hu⟩
  have h_norm := evenPermutations_normSq _ _ _ hu
  rw [h_norm]
  cases s0 <;> cases s1 <;> cases s2 <;> { dsimp; simp only [neg_div, neg_sq, golden_ratio_norm_sq_sum] }


lemma binaryTetrahedralUnits_normSq {u : ℍ[ℝ]} (h : u ∈ binaryTetrahedralUnits) :
    Quaternion.normSq u = 1 := by
  simp only [binaryTetrahedralUnits, Finset.mem_union] at h
  rcases h with hL | hH
  · exact lipschitzUnits_normSq hL
  · exact hurwitzUnits_normSq hH

lemma binaryIcosahedralUnits_normSq {u : ℍ[ℝ]} (h : u ∈ binaryIcosahedralUnits) :
    Quaternion.normSq u = 1 := by
  simp only [binaryIcosahedralUnits, Finset.mem_union] at h
  rcases h with hT | hI
  · exact binaryTetrahedralUnits_normSq hT
  · exact icosahedralUnits_normSq hI

/-- Coercion from a quaternion with unit norm into the unit group `ℍ[ℝ]ˣ`. -/
def toUnit (u : ℍ[ℝ]) (h : Quaternion.normSq u = 1) : ℍ[ℝ]ˣ :=
  ⟨u, star u, by rw [Quaternion.self_mul_star, h, Quaternion.coe_one],
              by rw [Quaternion.star_mul_self, h, Quaternion.coe_one]⟩

lemma toUnit_injective {u₁ u₂ : ℍ[ℝ]} (h₁ : Quaternion.normSq u₁ = 1) (h₂ : Quaternion.normSq u₂ = 1)
    (h : toUnit u₁ h₁ = toUnit u₂ h₂) : u₁ = u₂ := by
  have : (toUnit u₁ h₁).val = (toUnit u₂ h₂).val := by rw [h]
  exact this

/-- The finset of 120 unit quaternions in `ℍ[ℝ]ˣ`. -/
def binaryIcosahedralFinset : Finset ℍ[ℝ]ˣ :=
  binaryIcosahedralUnits.attach.map ⟨fun ⟨u, hu⟩ => toUnit u (binaryIcosahedralUnits_normSq hu),
    fun ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ h => by
      simp only [toUnit, Units.ext_iff] at h
      exact Subtype.ext h⟩

/-- The binary icosahedral group $I^* \subset ℍ[ℝ]^\times$, defined as the subgroup generated
by the 120 binary icosahedral unit quaternions. -/
def binaryIcosahedral : Subgroup ℍ[ℝ]ˣ :=
  Subgroup.closure (binaryIcosahedralFinset : Set ℍ[ℝ]ˣ)

/-- The binary tetrahedral group $2T \subset ℍ[ℝ]^\times$, defined as the subgroup generated
by the 24 binary tetrahedral unit quaternions. -/
def binaryTetrahedralFinset : Finset ℍ[ℝ]ˣ :=
  binaryTetrahedralUnits.attach.map ⟨fun ⟨u, hu⟩ => toUnit u (binaryTetrahedralUnits_normSq hu),
    fun ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ h => by
      simp only [toUnit, Units.ext_iff] at h
      exact Subtype.ext h⟩

/-- The binary tetrahedral group $2T \le ℍ[ℝ]^\times$. -/
def binaryTetrahedral : Subgroup ℍ[ℝ]ˣ :=
  Subgroup.closure (binaryTetrahedralFinset : Set ℍ[ℝ]ˣ)

/-- Binary tetrahedral is a subgroup of binary icosahedral: $2T \le I^*$. -/
theorem binaryTetrahedral_le_binaryIcosahedral : binaryTetrahedral ≤ binaryIcosahedral := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [binaryTetrahedralFinset, Finset.mem_coe, Finset.mem_map, Finset.mem_attach,
    true_and, Subtype.exists] at hx
  rcases hx with ⟨u, hu, rfl⟩
  simp only [binaryIcosahedralFinset, Finset.mem_coe, Finset.mem_map, Finset.mem_attach,
    true_and, Subtype.exists]
  refine ⟨u, Finset.mem_union_left _ hu, ?_⟩
  rfl

/-- Group closure property: identity element. -/
theorem mem_binaryIcosahedral_one : (1 : ℍ[ℝ]ˣ) ∈ binaryIcosahedral :=
  binaryIcosahedral.one_mem

/-- Group closure property: closure under quaternion multiplication. -/
theorem mem_binaryIcosahedral_mul {g h : ℍ[ℝ]ˣ} (hg : g ∈ binaryIcosahedral) (hh : h ∈ binaryIcosahedral) :
    g * h ∈ binaryIcosahedral :=
  binaryIcosahedral.mul_mem hg hh

/-- Group closure property: closure under quaternion inversion. -/
theorem mem_binaryIcosahedral_inv {g : ℍ[ℝ]ˣ} (hg : g ∈ binaryIcosahedral) :
    g⁻¹ ∈ binaryIcosahedral :=
  binaryIcosahedral.inv_mem hg

/-- Central inversion element -1 in ℍ[ℝ]ˣ. -/
def centralInv : ℍ[ℝ]ˣ :=
  toUnit (q (-1) 0 0 0) (by rw [normSq_q]; ring)

lemma mem_binaryIcosahedral_centralInv : centralInv ∈ binaryIcosahedral := by
  apply Subgroup.subset_closure
  simp only [binaryIcosahedralFinset, Finset.mem_coe, Finset.mem_map, Finset.mem_attach,
    true_and, Subtype.exists]
  refine ⟨q (-1) 0 0 0, ?_, ?_⟩
  · simp only [binaryIcosahedralUnits, binaryTetrahedralUnits, lipschitzUnits,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · rfl
