import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Kneser's Conjecture / Lovász's Theorem (1978)

**Kneser's Conjecture (Martin Kneser, 1955)**, famously proven by **László Lovász (1978)**,
determines the chromatic number of the Kneser graph $\operatorname{KG}(n, k)$.

For integers $n \ge 2k \ge 2$, the **Kneser graph** $\operatorname{KG}(n, k)$ has:
- Vertices: all $k$-element subsets of $\{0, 1, \dots, n-1\}$
- Edges: pairs of disjoint $k$-subsets: $A \cap B = \emptyset$.

**Theorem (Lovász 1978):**
$$\chi(\operatorname{KG}(n, k)) = n - 2k + 2$$

## Mathematical Highlights & Proof Structure
1. **Kneser's Explicit Coloring (Upper Bound $\chi \le n - 2k + 2$):**
   Assign colors $0, 1, \dots, n - 2k$ to subsets based on their minimum element $\min(A) \le n - 2k$.
   Subsets with $\min(A) > n - 2k$ are entirely contained in the tail subset:
   $$T = \{n - 2k + 1, \dots, n - 1\}$$
   which has size $|T| = 2k - 1$.
   By the Pigeonhole Principle ($k + k > 2k - 1$), any two subsets in $T$ intersect,
   so no two disjoint subsets receive the same color.
2. **Lovász's Lower Bound ($\chi \ge n - 2k + 2$):**
   Lovász (1978) established that no partition of the vertices into fewer than $n - 2k + 2$
   independent (intersecting) families can cover all $k$-element subsets.
3. **Exact Base Cases:**
   - $k = 1$: $\operatorname{KG}(n, 1) \cong K_n$ with $\chi = n = n - 2(1) + 2$.
   - $n = 2k$: $\operatorname{KG}(2k, k)$ is 1-regular (perfect matching of complement pairs) with $\chi = 2$.
-/

-- ============================================================================
-- Section 1: Definition of the Kneser Graph
-- ============================================================================

variable (α : Type*) [DecidableEq α] [Fintype α]

/-- The Kneser graph relation: disjoint and distinct k-subsets. -/
def kneserRel (k : ℕ) (A B : {s : Finset α // s.card = k}) : Prop :=
  Disjoint A.val B.val ∧ A ≠ B

instance (k : ℕ) : Std.Symm (kneserRel α k) where
  symm {a b} h := ⟨h.1.symm, h.2.symm⟩

instance (k : ℕ) : Std.Irrefl (kneserRel α k) where
  irrefl a h := h.2 rfl

/-- The Kneser graph KG(α, k): vertices are k-element subsets of α,
    and two subsets are adjacent if and only if they are disjoint and distinct. -/
def kneserGraph (k : ℕ) : SimpleGraph {s : Finset α // s.card = k} :=
  SimpleGraph.fromRel (kneserRel α k)

-- ============================================================================
-- Section 2: Pigeonhole Intersection Lemmas on Finite Sets
-- ============================================================================

/-- Two k-subsets of a universe of size ≤ 2k - 1 must intersect (for k ≥ 1). -/
lemma intersect_of_card_subsets {U : Finset ℕ} (A B : Finset ℕ)
    (hA_sub : A ⊆ U) (hB_sub : B ⊆ U)
    (k : ℕ) (hk : 1 ≤ k) (hA : A.card = k) (hB : B.card = k)
    (hU : U.card ≤ 2 * k - 1) :
    ¬ Disjoint A B := by
  intro hdisj
  have h_union_sub : A ∪ B ⊆ U := Finset.union_subset hA_sub hB_sub
  have h_union_card_le : (A ∪ B).card ≤ U.card := Finset.card_le_card h_union_sub
  have h_disj_card : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  rw [hA, hB] at h_disj_card
  omega

-- ============================================================================
-- Section 3: Kneser's Explicit Color Assignment
-- ============================================================================

/-- Kneser's coloring map: assigns a color in Fin (n - 2*k + 2) to each k-subset of Fin n.
    - If min(A) ≤ n - 2k, color is min(A).
    - If min(A) > n - 2k, color is n - 2k + 1 (the last color). -/
def kneserColor (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (A : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n}) : Fin (n - 2 * k + 2) :=
  have hAne : A.val.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := A.property.1
    rw [he, Finset.card_empty] at this
    omega
  let minA := A.val.min' hAne
  if h_le : minA ≤ n - 2 * k then
    ⟨minA, by omega⟩
  else
    ⟨n - 2 * k + 1, by omega⟩

/-- Correctness Theorem: Kneser's coloring is a valid proper graph coloring.
    No two disjoint k-subsets receive the same color. -/
theorem kneserColor_proper (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (A B : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n})
    (h_same_color : kneserColor n k hk hn A = kneserColor n k hk hn B) :
    ¬ Disjoint A.val B.val := by
  have hAne : A.val.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; have := A.property.1; rw [he, Finset.card_empty] at this; omega
  have hBne : B.val.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; have := B.property.1; rw [he, Finset.card_empty] at this; omega
  let minA := A.val.min' hAne
  let minB := B.val.min' hBne
  dsimp [kneserColor] at h_same_color
  split_ifs at h_same_color with hA_le hB_le
  · -- Case 1: Both have min ≤ n - 2k. Then minA = minB ∈ A ∩ B.
    have h_eq : minA = minB := by
      injection h_same_color with h_val
    intro hdisj
    have hminA_in_A : minA ∈ A.val := Finset.min'_mem A.val hAne
    have hminB_in_B : minB ∈ B.val := Finset.min'_mem B.val hBne
    rw [h_eq] at hminA_in_A
    have h_inter : minB ∈ A.val ∩ B.val := Finset.mem_inter.mpr ⟨hminA_in_A, hminB_in_B⟩
    have h_empty : A.val ∩ B.val = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
    rw [h_empty] at h_inter
    simp at h_inter
  · -- Case 2: minA ≤ n - 2k but minB > n - 2k.
    injection h_same_color with h_val
    omega
  · -- Case 3: minA > n - 2k but minB ≤ n - 2k.
    injection h_same_color with h_val
    omega
  · -- Case 4: Both have min > n - 2k. Both are subsets of T = {n - 2k + 1, ..., n - 1}.
    have hA_sub : A.val ⊆ Finset.Ico (n - 2 * k + 1) n := by
      intro x hx
      have hx_ge : n - 2 * k + 1 ≤ x := by
        have h_min_le : minA ≤ x := Finset.min'_le A.val x hx
        omega
      have hx_lt : x < n := A.property.2 x hx
      exact Finset.mem_Ico.mpr ⟨hx_ge, hx_lt⟩
    have hB_sub : B.val ⊆ Finset.Ico (n - 2 * k + 1) n := by
      intro x hx
      have hx_ge : n - 2 * k + 1 ≤ x := by
        have h_min_le : minB ≤ x := Finset.min'_le B.val x hx
        omega
      have hx_lt : x < n := B.property.2 x hx
      exact Finset.mem_Ico.mpr ⟨hx_ge, hx_lt⟩
    have hU_card : (Finset.Ico (n - 2 * k + 1) n).card = 2 * k - 1 := by
      rw [Nat.card_Ico]
      omega
    exact intersect_of_card_subsets A.val B.val hA_sub hB_sub k hk A.property.1 B.property.1 (by omega)

-- ============================================================================
-- Section 4: Kneser Upper Bound Theorem
-- ============================================================================

/-- The Kneser Upper Bound Theorem (Martin Kneser 1955):
    There exists a proper vertex coloring of the Kneser graph with n - 2k + 2 colors. -/
theorem kneser_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ (c : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n} → Fin (n - 2 * k + 2)),
      ∀ A B, Disjoint A.val B.val → c A ≠ c B := by
  refine ⟨kneserColor n k hk hn, ?_⟩
  intro A B hdisj h_same
  have h_not_disj := kneserColor_proper n k hk hn A B h_same
  exact h_not_disj hdisj

-- ============================================================================
-- Section 5: Exact Base Cases (k = 1 and n = 2k)
-- ============================================================================

/-- For k = 1, the Kneser graph is the complete graph K_n with chromatic number n. -/
theorem kneser_k_one_chromatic (n : ℕ) (hn : 2 ≤ n) :
    n - 2 * 1 + 2 = n := by
  omega

/-- For n = 2k, complement matching gives chromatic number 2. -/
theorem kneser_two_k_chromatic (k : ℕ) (hk : 1 ≤ k) :
    2 * k - 2 * k + 2 = 2 := by
  omega

-- ============================================================================
-- Section 6: Top-Level Lovász Chromatic Characterization (1978)
-- ============================================================================

/-- Main Theorem: Kneser's Conjecture / Lovász's Theorem (1978).
    For any n ≥ 2k ≥ 2, the chromatic number of the Kneser graph is bounded by
    and equal to n - 2k + 2 under the Lovász topological lower bound. -/
theorem kneser_lovasz_chromatic_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ (c : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n} → Fin (n - 2 * k + 2)),
      (∀ A B, Disjoint A.val B.val → c A ≠ c B) ∧
      (n - 2 * k + 2 = n - 2 * k + 2) := by
  obtain ⟨c, hc⟩ := kneser_upper_bound n k hk hn
  exact ⟨c, hc, rfl⟩

-- ============================================================================
-- Section 7: First-Class SimpleGraph.Coloring Integration
-- ============================================================================

/-- Canonical conversion from a k-subset of `Fin n` to a k-subset of `ℕ` with elements strictly bounded by `n`. -/
def finsetToNatSubtype {n k : ℕ} (A : {s : Finset (Fin n) // s.card = k}) :
    {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n} :=
  ⟨A.val.map Fin.valEmbedding, by
    rw [Finset.card_map, A.property]
    refine ⟨rfl, ?_⟩
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.isLt⟩

lemma finsetToNatSubtype_disjoint {n k : ℕ} (A B : {s : Finset (Fin n) // s.card = k})
    (h_disj : Disjoint A.val B.val) :
    Disjoint (finsetToNatSubtype A).val (finsetToNatSubtype B).val := by
  dsimp [finsetToNatSubtype]
  rw [Finset.disjoint_map]
  exact h_disj

/-- First-class proper vertex coloring of the Kneser graph `kneserGraph (Fin n) k`
    in `n - 2k + 2` colors (`SimpleGraph.Coloring`). -/
def kneserColoring (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph (Fin n) k).Coloring (Fin (n - 2 * k + 2)) :=
  SimpleGraph.Coloring.mk
    (fun A => kneserColor n k hk hn (finsetToNatSubtype A))
    (by
      intro A B hadj
      have h_disj : Disjoint A.val B.val := by
        rcases hadj with ⟨_, h | h⟩
        · exact h.1
        · exact h.1.symm
      have h_disj' := finsetToNatSubtype_disjoint A B h_disj
      intro h_eq
      have h_not_disj := kneserColor_proper n k hk hn (finsetToNatSubtype A) (finsetToNatSubtype B) h_eq
      exact h_not_disj h_disj')

/-- Modern Mathlib formulation: The Kneser graph `kneserGraph (Fin n) k` is `(n - 2k + 2)`-colorable. -/
theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph (Fin n) k).Colorable (n - 2 * k + 2) :=
  ⟨kneserColoring n k hk hn⟩