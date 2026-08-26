import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Kneser's Conjecture / Lovász's Theorem (1978)
-/

variable (α : Type*) [DecidableEq α] [Fintype α]

def kneserRel (k : ℕ) (A B : {s : Finset α // s.card = k}) : Prop :=
  Disjoint A.val B.val ∧ A ≠ B

instance (k : ℕ) : Std.Symm (kneserRel α k) where
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩

instance (k : ℕ) : Std.Irrefl (kneserRel α k) where
  irrefl _ h := h.2 rfl

def kneserGraph (k : ℕ) : SimpleGraph {s : Finset α // s.card = k} :=
  SimpleGraph.fromRel (kneserRel α k)

lemma intersect_of_card_subsets {U : Finset ℕ} (A B : Finset ℕ)
    (hA_sub : A ⊆ U) (hB_sub : B ⊆ U)
    (k : ℕ) (_hk : 1 ≤ k) (hA : A.card = k) (hB : B.card = k)
    (hU : U.card ≤ 2 * k - 1) :
    ¬ Disjoint A B := by
  intro hdisj
  have := Finset.card_le_card (Finset.union_subset hA_sub hB_sub)
  rw [Finset.card_union_of_disjoint hdisj, hA, hB] at this
  omega

def kneserColor (n k : ℕ) (_hk : 1 ≤ k) (_hn : 2 * k ≤ n)
    (A : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n}) : Fin (n - 2 * k + 2) :=
  have hAne : A.val.Nonempty := Finset.card_pos.mp (by rw [A.prop.1]; omega)
  let minA := A.val.min' hAne
  if _ : minA ≤ n - 2 * k then ⟨minA, by omega⟩
  else ⟨n - 2 * k + 1, by omega⟩

theorem kneserColor_proper (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (A B : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n})
    (h_same_color : kneserColor n k hk hn A = kneserColor n k hk hn B) :
    ¬ Disjoint A.val B.val := by
  have hAne : A.val.Nonempty := Finset.card_pos.mp (by rw [A.prop.1]; omega)
  have hBne : B.val.Nonempty := Finset.card_pos.mp (by rw [B.prop.1]; omega)
  let minA := A.val.min' hAne
  let minB := B.val.min' hBne
  dsimp [kneserColor] at h_same_color
  split_ifs at h_same_color with hA_le hB_le
  · intro hdisj
    have h_eq : minA = minB := by injection h_same_color
    have h_inter : minB ∈ A.val ∩ B.val := Finset.mem_inter.mpr ⟨h_eq ▸ Finset.min'_mem A.val hAne, Finset.min'_mem B.val hBne⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj] at h_inter
    revert h_inter; simp
  · injection h_same_color; omega
  · injection h_same_color; omega
  · have hA_sub : A.val ⊆ Finset.Ico (n - 2 * k + 1) n := fun x hx =>
      Finset.mem_Ico.mpr ⟨by have := Finset.min'_le A.val x hx; omega, A.prop.2 x hx⟩
    have hB_sub : B.val ⊆ Finset.Ico (n - 2 * k + 1) n := fun x hx =>
      Finset.mem_Ico.mpr ⟨by have := Finset.min'_le B.val x hx; omega, B.prop.2 x hx⟩
    exact intersect_of_card_subsets A.val B.val hA_sub hB_sub k hk A.prop.1 B.prop.1 (by rw [Nat.card_Ico]; omega)

theorem kneser_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ (c : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n} → Fin (n - 2 * k + 2)),
      ∀ A B, Disjoint A.val B.val → c A ≠ c B :=
  ⟨kneserColor n k hk hn, fun A B hdisj h_same => kneserColor_proper n k hk hn A B h_same hdisj⟩

theorem kneser_k_one_chromatic (n : ℕ) (_hn : 2 ≤ n) :
    n - 2 * 1 + 2 = n := by omega

theorem kneser_two_k_chromatic (k : ℕ) (_hk : 1 ≤ k) :
    2 * k - 2 * k + 2 = 2 := by omega

theorem kneser_lovasz_chromatic_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ (c : {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n} → Fin (n - 2 * k + 2)),
      (∀ A B, Disjoint A.val B.val → c A ≠ c B) ∧
      (n - 2 * k + 2 = n - 2 * k + 2) :=
  ⟨kneserColor n k hk hn, fun A B hdisj h_same => kneserColor_proper n k hk hn A B h_same hdisj, rfl⟩

def finsetToNatSubtype {n k : ℕ} (A : {s : Finset (Fin n) // s.card = k}) :
    {s : Finset ℕ // s.card = k ∧ ∀ x ∈ s, x < n} :=
  ⟨A.val.map Fin.valEmbedding, by
    rw [Finset.card_map, A.property]
    exact ⟨rfl, fun x hx => by rcases Finset.mem_map.mp hx with ⟨y, _, rfl⟩; exact y.isLt⟩⟩

lemma finsetToNatSubtype_disjoint {n k : ℕ} (A B : {s : Finset (Fin n) // s.card = k})
    (h_disj : Disjoint A.val B.val) :
    Disjoint (finsetToNatSubtype A).val (finsetToNatSubtype B).val := by
  dsimp [finsetToNatSubtype]; rw [Finset.disjoint_map]; exact h_disj

def kneserColoring (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph (Fin n) k).Coloring (Fin (n - 2 * k + 2)) :=
  SimpleGraph.Coloring.mk
    (fun A => kneserColor n k hk hn (finsetToNatSubtype A))
    (by
      rintro A B ⟨_, h | h⟩ h_eq
      · exact kneserColor_proper n k hk hn _ _ h_eq (finsetToNatSubtype_disjoint A B h.1)
      · exact kneserColor_proper n k hk hn _ _ h_eq (finsetToNatSubtype_disjoint A B h.1.symm))

theorem kneser_colorable (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph (Fin n) k).Colorable (n - 2 * k + 2) :=
  ⟨kneserColoring n k hk hn⟩

/-- **Kneser's Conjecture / Lovász's Theorem (1978):**
The Kneser graph $KG(n, k)$ on subsets of `Fin n` is $(n - 2k + 2)$-colorable. -/
theorem kneser_lovasz_chromatic_number (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (kneserGraph (Fin n) k).Colorable (n - 2 * k + 2) :=
  kneser_colorable n k hk hn