import Formalization.TuckersLemma.Basic
import Formalization.TuckersLemma.DoubleCounting
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Relation

open Finset

/-!
# Boundary Cycle, Telescoping Parity & Unconditional 2D Tucker's Lemma

This module establishes the "missing bridge" connecting 1D parity arguments and 2D
double-counting on edge-pseudomanifolds to prove the **full, unconditional 2D Tucker's Lemma**:

1. **Boundary Door Potentials & Door Steps:**
   - `boundaryDoorPotential x`: potential function on vertex labels $\{1, -1, 2, -2\}$.
   - `doorStep a b`: indicator for transitions $\{1, 2\}$ and $\{-1, -2\}$.
   - `doorStep_eq_potential_mod_two`: local potential-step equality modulo 2.
   - `potential_antipodal_mod_two`: antipodal boundary points have odd potential sum.

2. **Cyclic Boundary Pseudomanifolds (`CyclicBoundaryPseudomanifold2D`):**
   - Triangulation with an explicit boundary cycle `boundaryCycle : Fin (2 * k) → V`.
   - Injective cycle of length $2k$.
   - Boundary edges are precisely the cycle segments $\{c(i), c(i + 1)\}$.
   - Decoupled from any global involution on $V$.
   - `SymmetricDiskTriangulation2D` provided as alias for backwards compatibility.

3. **Boundary Graph Properties:**
   - `boundary_subset_edges`: boundary edges belong to `T.edges`.
   - `boundary_vertex_degree_two`: 2-regularity of the boundary cycle for $k > 1$.

4. **Telescoping Parity Along a Path:**
   - `path_doorStep_sum_mod_two`: telescoping sum of door steps along any path.
   - `path_doorStep_sum_odd_of_antipodal`: odd sum when endpoints are antipodal.

5. **Boundary Door Parity Theorem:**
   - `boundary_doors_odd_of_no_comp`: if $L$ is antipodal on the boundary cycle and has
     no complementary boundary edges, then the number of boundary doors is odd (1 mod 2).

6. **Full Unconditional 2D Tucker's Lemma:**
   - `tuckers_lemma_2d`: every cyclic boundary pseudomanifold with an antipodal boundary labeling
     contains a complementary edge in `T.edges`, with NO assumptions on boundary door parity!

7. **Combinatorial 2-Disk Characterization (`IsCombinatorialDisk2D`):**
   - Formal vertex link conditions (circle for interior, path for boundary) and connectedness.
-/

namespace TuckersLemma

lemma neZero_two_mul_of_pos {k : ℕ} (hk : 0 < k) : NeZero (2 * k) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos Nat.zero_lt_two hk)⟩

/-- Half-shift index in `Fin (2 * k)` representing antipodal antiposition along the cycle. -/
def finHalfShift (k : ℕ) (hk : 0 < k) : Fin (2 * k) :=
  ⟨k, (Nat.two_mul k).symm ▸ Nat.lt_add_of_pos_right hk⟩

/-- Potential function on labels in $\{1, -1, 2, -2\}$. Takes value 1 at $-1$ and $2$, and 0 otherwise. -/
def boundaryDoorPotential (x : ℤ) : ℕ := if x = -1 ∨ x = 2 then 1 else 0

/-- Door step indicator between two labels: 1 if the unordered pair is $\{1, 2\}$ or $\{-1, -2\}$, 0 otherwise. -/
def doorStep (a b : ℤ) : ℕ :=
  if ({a, b} : Finset ℤ) = {1, 2} ∨ ({a, b} : Finset ℤ) = {-1, -2} then 1 else 0

/-- Local door-step / potential equality modulo 2:
    for non-complementary adjacent vertices, the door step parity equals the sum of potentials modulo 2. -/
lemma doorStep_eq_potential_mod_two (a b : ℤ)
    (ha : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2)
    (hb : b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2)
    (h_nocomp : a ≠ -b) :
    doorStep a b % 2 = (boundaryDoorPotential a + boundaryDoorPotential b) % 2 := by
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  revert h_nocomp <;> decide

/-- Antipodal points have odd potential sum modulo 2. -/
lemma potential_antipodal_mod_two (x : ℤ)
    (hx : x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2) :
    (boundaryDoorPotential (-x) + boundaryDoorPotential x) % 2 = 1 := by
  rcases hx with rfl | rfl | rfl | rfl <;> decide

section BoundaryCycle

variable {V : Type*} [DecidableEq V]

/-- An abstract 2-dimensional edge-pseudomanifold equipped with an explicit cyclic boundary of length $2k$.
    The boundary edges form a single simple cycle of even length $2k$.
    Crucially, this decouples the boundary structure from any requirement of a global involution on the
    interior vertices $V$, isolating the exact combinatorial boundary topology needed for Tucker's Lemma. -/
structure CyclicBoundaryPseudomanifold2D (V : Type*) [DecidableEq V] extends EdgePseudomanifold2D V where
  k : ℕ
  hk : 0 < k
  boundaryCycle : Fin (2 * k) → V
  boundary_injective : Function.Injective boundaryCycle
  boundary_edges :
    toEdgePseudomanifold2D.boundaryEdges =
      Finset.image (fun i : Fin (2 * k) => ({boundaryCycle i, boundaryCycle (finRotate (2 * k) i)} : Finset V)) Finset.univ

/-- Backward-compatible alias for `CyclicBoundaryPseudomanifold2D`.
    In earlier formulations, this was named `SymmetricDiskTriangulation2D`; however, the combinatorial
    proof of Tucker's Lemma does not require global antipodal symmetry on the interior of the disk,
    only that the 1-dimensional boundary pseudomanifold cycle admits an antipodal labeling. -/
abbrev SymmetricDiskTriangulation2D := CyclicBoundaryPseudomanifold2D

instance (T : CyclicBoundaryPseudomanifold2D V) : NeZero (2 * T.k) := neZero_two_mul_of_pos T.hk

/-- The cycle boundary edges can be equivalently indexed via successor `i + 1`. -/
lemma boundary_edges_eq (T : CyclicBoundaryPseudomanifold2D V) :
    T.boundaryEdges = Finset.image (fun i : Fin (2 * T.k) => ({T.boundaryCycle i, T.boundaryCycle (i + 1)} : Finset V)) Finset.univ := by
  have h := T.boundary_edges
  simp_rw [finRotate_apply] at h
  exact h

/-- The vertices belonging to the boundary cycle. -/
def boundaryVertices (T : CyclicBoundaryPseudomanifold2D V) : Finset V :=
  Finset.image T.boundaryCycle Finset.univ

/-- Boundary edges are contained in the full edge set `T.edges`. -/
lemma boundary_subset_edges (T : CyclicBoundaryPseudomanifold2D V) :
    T.boundaryEdges ⊆ T.edges :=
  Finset.filter_subset _ _

/-! ### Graph-Theoretic Properties of the Boundary Cycle -/

lemma finset_pair_eq_pair_iff {α : Type*} [DecidableEq α] {a b c d : α} :
    ({a, b} : Finset α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← Finset.coe_inj]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.pair_eq_pair_iff]

lemma fin_ne_add_two {k : ℕ} (hk : 1 < k) [NeZero (2 * k)] (j : Fin (2 * k)) :
    j ≠ j + 1 + 1 := by
  intro h
  have h_val := congrArg Fin.val h
  have h_one : ((1 : Fin (2 * k))).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have h_add2 : (j + 1 + 1).val = (j.val + 2) % (2 * k) := by
    rw [Fin.val_add, Fin.val_add, h_one, Nat.add_mod ((j.val + 1) % (2 * k)) 1, Nat.mod_mod, ← Nat.add_mod]
  have hdvd : 2 * k ∣ 2 := by
    have hm : j.val + 2 ≡ j.val [MOD 2 * k] := by rw [Nat.ModEq, ← h_add2, h_val.symm, Nat.mod_eq_of_lt j.isLt]
    have := hm.symm.dvd'
    rwa [show (j.val + 2) - j.val = 2 by omega] at this
  have := Nat.le_of_dvd (by omega) hdvd
  omega

lemma fin_ne_succ {n : ℕ} [NeZero n] (hn : 1 < n) (i : Fin n) : i ≠ i + 1 := by
  intro h
  have h_val := congrArg Fin.val h
  have h_one : ((1 : Fin n)).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt hn]
  rw [Fin.val_add, h_one] at h_val
  have hdvd : n ∣ 1 := by
    have hm : i.val + 1 ≡ i.val [MOD n] := by rw [Nat.ModEq, h_val.symm, Nat.mod_eq_of_lt i.isLt]
    have := hm.symm.dvd'
    rwa [show (i.val + 1) - i.val = 1 by omega] at this
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The cycle edge parameterization `i ↦ {c(i), c(i + 1)}` is injective when $k > 1$. -/
lemma boundary_edge_map_inj (T : CyclicBoundaryPseudomanifold2D V) (hk : 1 < T.k) :
    Function.Injective (fun i : Fin (2 * T.k) => ({T.boundaryCycle i, T.boundaryCycle (i + 1)} : Finset V)) := by
  intro i j hij
  rw [finset_pair_eq_pair_iff] at hij
  rcases hij with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact T.boundary_injective h1
  · have hi_eq := T.boundary_injective h1
    have hj_eq := T.boundary_injective h2
    rw [hi_eq] at hj_eq
    exfalso
    exact fin_ne_add_two hk j hj_eq.symm

/-- 2-regularity of the boundary cycle:
    for any $k > 1$, each boundary vertex is incident to exactly 2 boundary edges. -/
lemma boundary_vertex_degree_two (T : CyclicBoundaryPseudomanifold2D V) (hk : 1 < T.k)
    (v : V) (hv : v ∈ boundaryVertices T) :
    (T.boundaryEdges.filter (fun e => v ∈ e)).card = 2 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
  have h_bd_edges : T.boundaryEdges =
      Finset.image (fun i : Fin (2 * T.k) => {T.boundaryCycle i, T.boundaryCycle (i + 1)}) Finset.univ :=
    boundary_edges_eq T
  rw [h_bd_edges, Finset.filter_image]
  have h_inj := boundary_edge_map_inj T hk
  rw [Finset.card_image_of_injective _ h_inj]
  have h_set : (Finset.univ.filter (fun i : Fin (2 * T.k) => T.boundaryCycle j ∈ ({T.boundaryCycle i, T.boundaryCycle (i + 1)} : Finset V))) =
      {j, (finRotate (2 * T.k)).symm j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hi
      rcases hi with h | h
      · left; exact (T.boundary_injective h).symm
      · right
        have h_eq := T.boundary_injective h
        rw [← finRotate_apply] at h_eq
        rw [h_eq, Equiv.symm_apply_apply]
    · rintro (rfl | rfl)
      · left; rfl
      · right
        have h_rot : (finRotate (2 * T.k)) ((finRotate (2 * T.k)).symm j) = j :=
          (finRotate (2 * T.k)).apply_symm_apply j
        rw [finRotate_apply] at h_rot
        rw [h_rot]
  rw [h_set]
  apply Finset.card_pair
  intro h_eq
  have h_rot : (finRotate (2 * T.k)) ((finRotate (2 * T.k)).symm j) = j :=
    (finRotate (2 * T.k)).apply_symm_apply j
  rw [← h_eq] at h_rot
  rw [finRotate_apply] at h_rot
  exact fin_ne_succ (by omega) j h_rot.symm

/-! ### Telescoping Parity Along a Path -/

/-- Telescoping parity along a sequence:
    sum of door steps modulo 2 equals the potential difference at the endpoints. -/
theorem path_doorStep_sum_mod_two (m : ℕ) (s : Fin (m + 1) → ℤ)
    (h_range : ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 2 ∨ s i = -2)
    (h_nocomp : ∀ i : Fin m, s i.castSucc ≠ - s i.succ) :
    (∑ i : Fin m, doorStep (s i.castSucc) (s i.succ)) % 2 =
    (boundaryDoorPotential (s 0) + boundaryDoorPotential (s (Fin.last m))) % 2 := by
  induction m with
  | zero =>
    have : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [this]
    simp
    omega
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have ih_s := ih (fun i => s i.succ) (fun i => h_range i.succ) (fun i => h_nocomp i.succ)
    have h0_step := doorStep_eq_potential_mod_two (s 0) (s 1) (h_range 0) (h_range 1) (h_nocomp 0)
    have h_cast0 : (Fin.castSucc (0 : Fin (m + 1)) : Fin (m + 2)) = 0 := rfl
    have h_succ0 : (Fin.succ (0 : Fin (m + 1)) : Fin (m + 2)) = 1 := rfl
    have h_last : (Fin.succ (Fin.last m)) = Fin.last (m + 1) := rfl
    have h_step_eq (i : Fin m) : (Fin.succ i).castSucc = (Fin.castSucc i).succ := rfl
    simp_rw [h_step_eq]
    rw [h_cast0, h_succ0]
    change (doorStep (s 0) (s 1) + ∑ i : Fin m, doorStep (s i.castSucc.succ) (s i.succ.succ)) % 2 =
      (boundaryDoorPotential (s 0) + boundaryDoorPotential (s (Fin.last (m + 1)))) % 2
    have h_s0 : s (Fin.succ 0) = s 1 := rfl
    rw [h_last, h_s0] at ih_s
    omega

/-- Odd door step sum when endpoints are antipodal. -/
theorem path_doorStep_sum_odd_of_antipodal (m : ℕ) (s : Fin (m + 1) → ℤ)
    (h_range : ∀ i, s i = 1 ∨ s i = -1 ∨ s i = 2 ∨ s i = -2)
    (h_nocomp : ∀ i : Fin m, s i.castSucc ≠ - s i.succ)
    (h_anti : s (Fin.last m) = - s 0) :
    (∑ i : Fin m, doorStep (s i.castSucc) (s i.succ)) % 2 = 1 := by
  rw [path_doorStep_sum_mod_two m s h_range h_nocomp]
  rw [h_anti, add_comm]
  exact potential_antipodal_mod_two (s 0) (h_range 0)

/-! ### Cycle Splitting and the Boundary Door Parity Theorem -/

lemma door_sum_two_halves (a b : ℤ)
    (ha : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2)
    (hb : b = 1 ∨ b = -1 ∨ b = 2 ∨ b = -2) :
    (if ({a, b} : Finset ℤ) = {1, 2} then 1 else 0) +
    (if ({-a, -b} : Finset ℤ) = {1, 2} then 1 else 0) =
    doorStep a b := by
  rcases ha with rfl | rfl | rfl | rfl <;>
  rcases hb with rfl | rfl | rfl | rfl <;>
  decide

lemma sum_fin_two_mul (k : ℕ) (g : Fin (2 * k) → ℕ) :
    (∑ x : Fin (2 * k), g x) =
    ∑ i : Fin k, (g ⟨i.val, by omega⟩ + g ⟨i.val + k, by omega⟩) := by
  have h_eq : 2 * k = k + k := by omega
  rw [← (finCongr h_eq.symm).sum_comp g]
  rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : finCongr h_eq.symm (Fin.castAdd k i) = ⟨i.val, by omega⟩ := by ext; simp
  have h2 : finCongr h_eq.symm (Fin.natAdd k i) = ⟨i.val + k, by omega⟩ := by ext; simp
  rw [h1, h2]

/-- The canonical half-cycle path of length $k$ along the boundary cycle. -/
def boundaryPath (T : CyclicBoundaryPseudomanifold2D V) (L : V → ℤ) :
    Fin (T.k + 1) → ℤ :=
  fun j => L (T.boundaryCycle ⟨j.val, by have := T.hk; omega⟩)

lemma j2_eq_j1_add_shift (k : ℕ) (hk : 0 < k) (i : Fin k) :
    have := neZero_two_mul_of_pos hk
    (⟨i.val + k, by omega⟩ : Fin (2 * k)) = ⟨i.val, by omega⟩ + finHalfShift k hk := by
  have := neZero_two_mul_of_pos hk
  ext
  rw [Fin.val_add]
  have : (finHalfShift k hk).val = k := rfl
  rw [this]
  have hlt : i.val + k < 2 * k := by have := i.isLt; omega
  rw [Nat.mod_eq_of_lt hlt]

lemma j1_succ_add_shift (k : ℕ) (hk : 0 < k) (i : Fin k) :
    have := neZero_two_mul_of_pos hk
    (⟨i.val + k, by omega⟩ : Fin (2 * k)) + 1 = (⟨i.val, by omega⟩ + 1) + finHalfShift k hk := by
  have := neZero_two_mul_of_pos hk
  rw [j2_eq_j1_add_shift k hk i]
  exact add_right_comm _ _ _

lemma isDoor_pair_eq (u v : V) (huv : u ≠ v) (L : V → ℤ) :
    isDoor L {u, v} ↔ ({L u, L v} : Finset ℤ) = {1, 2} := by
  dsimp [isDoor]
  have : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
  simp [this]

/-- If there are no complementary boundary edges, then $k > 1$.
    (At $k = 1$, the unique boundary edge is between antipodal vertices, hence complementary). -/
lemma k_ge_two_of_no_comp_boundary (T : CyclicBoundaryPseudomanifold2D V) (L : V → ℤ)
    (h_anti_bd : ∀ i : Fin (2 * T.k), L (T.boundaryCycle (i + finHalfShift T.k T.hk)) = - L (T.boundaryCycle i))
    (h_no_comp : ∀ e ∈ T.boundaryEdges, ¬ IsComplementaryEdge L e) :
    1 < T.k := by
  by_contra! h_k
  have hk1 : T.k = 1 := by have := T.hk; omega
  have h_edge : {T.boundaryCycle 0, T.boundaryCycle (0 + 1)} ∈ T.boundaryEdges := by
    rw [boundary_edges_eq T]
    apply Finset.mem_image_of_mem
    exact Finset.mem_univ 0
  apply h_no_comp {T.boundaryCycle 0, T.boundaryCycle (0 + 1)} h_edge
  have h0 : (0 : Fin (2 * T.k)) + finHalfShift T.k T.hk = 0 + 1 := by
    ext; simp [finHalfShift, hk1]
  refine ⟨T.boundaryCycle 0, T.boundaryCycle (0 + 1), by simp, by simp, ?_, ?_⟩
  · intro h_eq
    have := congrArg Fin.val (T.boundary_injective h_eq)
    simp [hk1] at this
  · have h_anti := h_anti_bd 0
    rw [h0] at h_anti
    omega

lemma boundaryPath_nocomp (T : CyclicBoundaryPseudomanifold2D V) (L : V → ℤ)
    (h_no_comp : ∀ e ∈ T.boundaryEdges, ¬ IsComplementaryEdge L e)
    (i : Fin T.k) :
    boundaryPath T L i.castSucc ≠ - boundaryPath T L i.succ := by
  intro h_comp
  have h_edge_mem : {T.boundaryCycle ⟨i.val, by have := T.hk; omega⟩,
                     T.boundaryCycle (⟨i.val, by have := T.hk; omega⟩ + 1)} ∈ T.boundaryEdges := by
    rw [boundary_edges_eq T]
    apply Finset.mem_image_of_mem
    exact Finset.mem_univ _
  have h_succ_val : (⟨i.val, by have := T.hk; omega⟩ + 1 : Fin (2 * T.k)) =
      ⟨i.val + 1, by have := T.hk; omega⟩ := by
    ext
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 * T.k by have := T.hk; omega),
        Nat.mod_eq_of_lt (show i.val + 1 < 2 * T.k by have := i.isLt; have := T.hk; omega)]
  apply h_no_comp _ h_edge_mem
  refine ⟨T.boundaryCycle ⟨i.val, by have := T.hk; omega⟩,
          T.boundaryCycle (⟨i.val, by have := T.hk; omega⟩ + 1),
          by simp, by simp, ?_, ?_⟩
  · intro h_eq
    have := congrArg Fin.val (T.boundary_injective h_eq)
    rw [h_succ_val] at this
    dsimp at this
    omega
  · change L (T.boundaryCycle ⟨i.castSucc.val, by have := T.hk; omega⟩) = - L (T.boundaryCycle (⟨i.val, by have := T.hk; omega⟩ + 1))
    rw [h_succ_val]
    exact h_comp

lemma boundaryPath_antipodal (T : CyclicBoundaryPseudomanifold2D V) (L : V → ℤ)
    (h_anti_bd : ∀ i : Fin (2 * T.k), L (T.boundaryCycle (i + finHalfShift T.k T.hk)) = - L (T.boundaryCycle i)) :
    boundaryPath T L (Fin.last T.k) = - boundaryPath T L 0 := by
  have h_add : (0 : Fin (2 * T.k)) + finHalfShift T.k T.hk = ⟨T.k, by have := T.hk; omega⟩ := by
    ext; simp [finHalfShift]
  have h := h_anti_bd 0
  rwa [h_add] at h

/-- **Boundary Door Parity Theorem:**
    In a cyclic boundary pseudomanifold `T`, if the vertex labeling `L : V → {±1, ±2}`
    is antipodal on the boundary cycle
    (`∀ i : Fin (2 * T.k), L (T.boundaryCycle (i + finHalfShift T.k T.hk)) = - L (T.boundaryCycle i)`)
    and there are no complementary boundary edges,
    then the total number of boundary doors is odd (1 mod 2). -/
theorem boundary_doors_odd_of_no_comp (T : CyclicBoundaryPseudomanifold2D V) (L : V → ℤ)
    (h_range : ∀ v, L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2)
    (h_anti_bd : ∀ i : Fin (2 * T.k), L (T.boundaryCycle (i + finHalfShift T.k T.hk)) = - L (T.boundaryCycle i))
    (h_no_comp : ∀ e ∈ T.boundaryEdges, ¬ IsComplementaryEdge L e) :
    (T.boundaryEdges.filter (isDoor L)).card % 2 = 1 := by
  have hk : 1 < T.k := k_ge_two_of_no_comp_boundary T L h_anti_bd h_no_comp
  have h_card_eq : (T.boundaryEdges.filter (isDoor L)).card =
      ∑ x : Fin (2 * T.k), if isDoor L {T.boundaryCycle x, T.boundaryCycle (x + 1)} then 1 else 0 := by
    rw [boundary_edges_eq T, Finset.filter_image,
        Finset.card_image_of_injective _ (boundary_edge_map_inj T hk), card_filter]
  rw [h_card_eq]
  let g := fun x : Fin (2 * T.k) => if isDoor L {T.boundaryCycle x, T.boundaryCycle (x + 1)} then 1 else 0
  change (∑ x : Fin (2 * T.k), g x) % 2 = 1
  rw [sum_fin_two_mul T.k g]
  have h_step_sum : (∑ i : Fin T.k, (g ⟨i.val, by omega⟩ + g ⟨i.val + T.k, by omega⟩)) =
      ∑ i : Fin T.k, doorStep (boundaryPath T L i.castSucc) (boundaryPath T L i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    let j1 : Fin (2 * T.k) := ⟨i.val, by have := T.hk; omega⟩
    let j2 : Fin (2 * T.k) := ⟨i.val + T.k, by have := T.hk; omega⟩
    have hj1_ne : T.boundaryCycle j1 ≠ T.boundaryCycle (j1 + 1) := by
      intro h
      have h_fin := T.boundary_injective h
      exact fin_ne_succ (by have := T.hk; omega) j1 h_fin
    have hj2_ne : T.boundaryCycle j2 ≠ T.boundaryCycle (j2 + 1) := by
      intro h
      have h_fin := T.boundary_injective h
      exact fin_ne_succ (by have := T.hk; omega) j2 h_fin
    have h_door1 : isDoor L {T.boundaryCycle j1, T.boundaryCycle (j1 + 1)} ↔
        ({L (T.boundaryCycle j1), L (T.boundaryCycle (j1 + 1))} : Finset ℤ) = {1, 2} :=
      isDoor_pair_eq (T.boundaryCycle j1) (T.boundaryCycle (j1 + 1)) hj1_ne L
    have h_door2 : isDoor L {T.boundaryCycle j2, T.boundaryCycle (j2 + 1)} ↔
        ({L (T.boundaryCycle j2), L (T.boundaryCycle (j2 + 1))} : Finset ℤ) = {1, 2} :=
      isDoor_pair_eq (T.boundaryCycle j2) (T.boundaryCycle (j2 + 1)) hj2_ne L
    have hj2_eq : j2 = j1 + finHalfShift T.k T.hk := j2_eq_j1_add_shift T.k T.hk i
    have hj2_succ_eq : j2 + 1 = (j1 + 1) + finHalfShift T.k T.hk := j1_succ_add_shift T.k T.hk i
    have hL_j2 : L (T.boundaryCycle j2) = - L (T.boundaryCycle j1) := by
      rw [hj2_eq]
      exact h_anti_bd j1
    have hL_j2_succ : L (T.boundaryCycle (j2 + 1)) = - L (T.boundaryCycle (j1 + 1)) := by
      rw [hj2_succ_eq]
      exact h_anti_bd (j1 + 1)
    dsimp [g]
    rw [if_congr h_door1 rfl rfl, if_congr h_door2 rfl rfl]
    rw [hL_j2, hL_j2_succ]
    have h_split := door_sum_two_halves (L (T.boundaryCycle j1)) (L (T.boundaryCycle (j1 + 1)))
      (h_range _) (h_range _)
    rw [h_split]
    have hj1_succ : (j1 + 1) = ⟨i.succ.val, by have := T.hk; omega⟩ := by
      ext
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2 * T.k by have := T.hk; omega),
          Nat.mod_eq_of_lt (show i.val + 1 < 2 * T.k by have := i.isLt; have := T.hk; omega)]
      rfl
    rw [hj1_succ]
    rfl
  rw [h_step_sum]
  have h_path_anti := boundaryPath_antipodal T L h_anti_bd
  have h_path_nocomp := boundaryPath_nocomp T L h_no_comp
  have h_path_range (j : Fin (T.k + 1)) :
      boundaryPath T L j = 1 ∨ boundaryPath T L j = -1 ∨
      boundaryPath T L j = 2 ∨ boundaryPath T L j = -2 :=
    h_range _
  exact path_doorStep_sum_odd_of_antipodal T.k (boundaryPath T L) h_path_range h_path_nocomp h_path_anti

/-- **Unconditional 2D Tucker's Lemma (Albert W. Tucker, 1945):**
    For any cyclic boundary pseudomanifold `T` and any vertex labeling `L : V → {±1, ±2}`
    that is antipodal on the boundary cycle
    (`∀ i : Fin (2 * T.k), L (T.boundaryCycle (i + finHalfShift T.k T.hk)) = - L (T.boundaryCycle i)`),
    there exists a complementary edge in `T.edges`.
    Proved without ANY artificial assumptions or preconditions on boundary door parity! -/
theorem tuckers_lemma_2d (T : CyclicBoundaryPseudomanifold2D V) (L : V → ℤ)
    (h_range : ∀ v, L v = 1 ∨ L v = -1 ∨ L v = 2 ∨ L v = -2)
    (h_anti_bd : ∀ i : Fin (2 * T.k), L (T.boundaryCycle (i + finHalfShift T.k T.hk)) = - L (T.boundaryCycle i)) :
    ∃ e ∈ T.edges, IsComplementaryEdge L e := by
  by_cases h_comp : ∃ e ∈ T.boundaryEdges, IsComplementaryEdge L e
  · obtain ⟨e, he_bd, he_comp⟩ := h_comp
    exact ⟨e, boundary_subset_edges T he_bd, he_comp⟩
  · have h_no_comp : ∀ e ∈ T.boundaryEdges, ¬ IsComplementaryEdge L e := by
      intro e he hc
      exact h_comp ⟨e, he, hc⟩
    have h_odd := boundary_doors_odd_of_no_comp T L h_range h_anti_bd h_no_comp
    exact tucker_2d_of_odd_boundary T.toEdgePseudomanifold2D L h_range h_odd

/-! ### Topological Disk Triangulation & Vertex Link Characterization -/

/-- Adjacency relation between vertices in an edge set `E`. -/
def GraphAdj (E : Finset (Finset V)) (u v : V) : Prop :=
  {u, v} ∈ E

/-- A graph `(V', E)` is connected if it is nonempty and any two vertices are connected by a path. -/
def IsConnectedGraph (V' : Finset V) (E : Finset (Finset V)) : Prop :=
  V'.Nonempty ∧ ∀ u ∈ V', ∀ w ∈ V', Relation.ReflTransGen (GraphAdj E) u w

/-- A 1D combinatorial circle (homeomorphic to $S^1$):
    a nonempty connected graph where every vertex has degree 2. -/
def IsCombinatorialCircle (V' : Finset V) (E : Finset (Finset V)) : Prop :=
  IsConnectedGraph V' E ∧
  ∀ u ∈ V', (E.filter (fun e => u ∈ e)).card = 2

/-- A 1D combinatorial path (homeomorphic to $[0, 1]$):
    a nonempty connected graph where exactly two boundary vertices have degree 1
    and all other internal vertices have degree 2. -/
def IsCombinatorialPath (V' : Finset V) (E : Finset (Finset V)) : Prop :=
  IsConnectedGraph V' E ∧
  (V'.filter (fun u => (E.filter (fun e => u ∈ e)).card = 1)).card = 2 ∧
  ∀ u ∈ V', (E.filter (fun e => u ∈ e)).card = 1 ∨ (E.filter (fun e => u ∈ e)).card = 2

/-- Link edges of a vertex `v` in an edge-pseudomanifold:
    the 2-element edges opposite to `v` in faces containing `v`. -/
def vertexLinkEdges (T : EdgePseudomanifold2D V) (v : V) : Finset (Finset V) :=
  (T.faces.filter (fun t => v ∈ t)).image (fun t => t.erase v)

/-- Vertices belonging to the link of `v`. -/
def vertexLinkVertices (T : EdgePseudomanifold2D V) (v : V) : Finset V :=
  (vertexLinkEdges T v).biUnion id

/-- All vertices participating in the 2D pseudomanifold. -/
def EdgePseudomanifold2D.vertices (T : EdgePseudomanifold2D V) : Finset V :=
  T.faces.biUnion id

/-- Formal topological manifold condition characterizing a true combinatorial 2-disk triangulation:
    1. **Connectedness**: The 1-skeleton of the complex is connected.
    2. **Interior Link Condition**: For every interior vertex (a vertex not on the boundary cycle),
       its link $\text{Lk}(v)$ is a combinatorial circle (homeomorphic to $S^1$).
    3. **Boundary Link Condition**: For every boundary vertex, its link $\text{Lk}(v)$ is a
       combinatorial path (homeomorphic to $I = [0, 1]$).
    Together with the cyclic boundary condition, these conditions ensure that the complex is a
    combinatorial 2-manifold with boundary homeomorphic to the closed unit disk $D^2$. -/
def IsCombinatorialDisk2D (T : CyclicBoundaryPseudomanifold2D V) : Prop :=
  IsConnectedGraph T.toEdgePseudomanifold2D.vertices T.edges ∧
  (∀ v ∈ T.toEdgePseudomanifold2D.vertices,
    if v ∈ boundaryVertices T then
      IsCombinatorialPath (vertexLinkVertices T.toEdgePseudomanifold2D v) (vertexLinkEdges T.toEdgePseudomanifold2D v)
    else
      IsCombinatorialCircle (vertexLinkVertices T.toEdgePseudomanifold2D v) (vertexLinkEdges T.toEdgePseudomanifold2D v))

end BoundaryCycle

end TuckersLemma
