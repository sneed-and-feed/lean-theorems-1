import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

open SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TutteOneFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
# Tutte's 1-Factor Theorem, Tutte–Berge Formula, and Petersen's Theorems

This module formalizes:
1. **1-Factors and Perfect Matchings** in simple graphs.
2. **Odd Components count** $q(G \setminus U)$.
3. **Tutte's 1-Factor Theorem**: $G$ has a 1-factor $\iff \forall U \subseteq V, q(G \setminus U) \le |U|$.
4. **Tutte–Berge Formula & Matching Defect**:
   $$\nu(G) = \frac{1}{2} \min_{U \subseteq V} (|V| + |U| - q(G \setminus U))$$
   $$\operatorname{matchingDefect}(G) = \max_{U \subseteq V} (q(G \setminus U) - |U|)$$
5. **Petersen's Bridgeless Cubic Theorem**: Every 3-regular bridgeless graph has a 1-factor.
6. **Petersen's 2-Factor Theorem**: Every $2r$-regular graph decomposes into 2-factors.
7. **Hall's Marriage Theorem from Tutte's Theorem**: Bipartite specialization.

## References
* W. T. Tutte (1947), *The factorization of linear graphs*, J. London Math. Soc., 22(2):107–111.
* C. Berge (1958), *Sur le couplage maximum d'un graphe*, C. R. Acad. Sci. Paris, 247:258–259.
* J. Petersen (1891), *Die Theorie der regulären graphs*, Acta Math., 15:193–220.
* P. Hall (1935), *On Representatives of Subsets*, J. London Math. Soc., 10(1):26–30.
-/

/-! ## 1. 1-Factors and Perfect Matchings -/

/-- A 1-factor of a simple graph `G` is a 1-regular spanning subgraph, i.e., a perfect matching. -/
def IsOneFactor {G : SimpleGraph V} (M : G.Subgraph) : Prop :=
  M.IsPerfectMatching

/-- A graph `G` has a 1-factor if there exists a spanning perfect matching. -/
def HasOneFactor (G : SimpleGraph V) : Prop :=
  ∃ M : G.Subgraph, M.IsPerfectMatching

/-! ## 2. Odd Connected Components -/

/-- The number of odd connected components of `G \ U`. -/
noncomputable def q (G : SimpleGraph V) (U : Set V) : ℕ :=
  (((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents).ncard

/-- Finset version of the number of odd components `q(G \ U)`. -/
noncomputable def oddCompCount (G : SimpleGraph V) (U : Finset V) : ℕ :=
  q G (U : Set V)

/-! ## 3. Necessity and Tutte's 1-Factor Theorem -/

/-- **Tutte's 1-Factor Theorem (Necessity Direction):**
If `G` has a 1-factor, then for every subset `U ⊆ V`, the number of odd components `q(G \ U) ≤ |U|`. -/
theorem tutte_necessity (G : SimpleGraph V) (hM : HasOneFactor G) (U : Set V) :
    q G U ≤ U.ncard := by
  rcases hM with ⟨M, hM⟩
  have hnot := not_isTutteViolator_of_isPerfectMatching hM U
  simp only [IsTutteViolator, not_lt] at hnot
  exact hnot

/-- If `G` has a 1-factor, the total vertex count `|V|` must be even. -/
theorem even_card_of_hasOneFactor (G : SimpleGraph V) (hM : HasOneFactor G) :
    Even (Fintype.card V) := by
  rcases hM with ⟨M, hM⟩
  exact hM.even_card

/-- **Tutte's 1-Factor Theorem (Equivalence):**
A graph `G` has a 1-factor if and only if for all subsets `U ⊆ V`, `q(G \ U) ≤ |U|`. -/
theorem tutte_1factor_theorem (G : SimpleGraph V) :
    HasOneFactor G ↔ ∀ U : Set V, q G U ≤ U.ncard := by
  constructor
  · intro hM U
    exact tutte_necessity G hM U
  · intro h
    have ht : ∀ U : Set V, ¬ G.IsTutteViolator U := by
      intro U
      simp only [IsTutteViolator, not_lt]
      exact h U
    exact SimpleGraph.tutte.mpr ht

/-! ## 4. Tutte–Berge Formula and Matching Defect -/

/-- Defect of a vertex subset `U` with respect to `G`: `q(G \ U) - |U|`. -/
noncomputable def defect (G : SimpleGraph V) (U : Finset V) : ℤ :=
  (q G (U : Set V) : ℤ) - (U.card : ℤ)

/-- Matching defect of a graph `G`: `max_{U ⊆ V} (q(G \ U) - |U|)`. -/
noncomputable def matchingDefect (G : SimpleGraph V) : ℤ :=
  Finset.univ.image (fun U : Finset V => defect G U) |>.max' (by simp)

/-- The Tutte-Berge bound quantity for a given subset `U`: `|V| + |U| - q(G \ U)`. -/
noncomputable def tutteBergeBound (G : SimpleGraph V) (U : Finset V) : ℤ :=
  (Fintype.card V : ℤ) + (U.card : ℤ) - (q G (U : Set V) : ℤ)

/-- The Tutte-Berge min quantity: `min_{U ⊆ V} (|V| + |U| - q(G \ U))`. -/
noncomputable def tutteBergeMin (G : SimpleGraph V) : ℤ :=
  Finset.univ.image (fun U : Finset V => tutteBergeBound G U) |>.min' (by simp)

theorem tutteBergeBound_eq (G : SimpleGraph V) (U : Finset V) :
    tutteBergeBound G U = (Fintype.card V : ℤ) - defect G U := by
  dsimp [tutteBergeBound, defect]
  ring

/-- The Tutte–Berge minimum is exactly `|V| - matchingDefect G`. -/
theorem tutte_berge_min_eq_card_sub_defect (G : SimpleGraph V) :
    tutteBergeMin G = (Fintype.card V : ℤ) - matchingDefect G := by
  have h_bound : ∀ U : Finset V, tutteBergeBound G U = (Fintype.card V : ℤ) - defect G U :=
    tutteBergeBound_eq G
  let S : Finset ℤ := Finset.univ.image (fun U : Finset V => defect G U)
  have hS_ne : S.Nonempty := by simp [S]
  let T : Finset ℤ := Finset.univ.image (fun U : Finset V => tutteBergeBound G U)
  have hT_ne : T.Nonempty := by simp [T]
  have hT_eq : T = S.image (fun d => (Fintype.card V : ℤ) - d) := by
    ext t
    simp only [T, S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨U, rfl⟩
      refine ⟨defect G U, ⟨U, rfl⟩, (h_bound U).symm⟩
    · rintro ⟨d, ⟨U, rfl⟩, rfl⟩
      refine ⟨U, h_bound U⟩
  have hmin : T.min' hT_ne = (Fintype.card V : ℤ) - S.max' hS_ne := by
    apply le_antisymm
    · have h_max_mem := Finset.max'_mem S hS_ne
      have : (Fintype.card V : ℤ) - S.max' hS_ne ∈ T := by
        rw [hT_eq]
        exact Finset.mem_image_of_mem _ h_max_mem
      exact Finset.min'_le T _ this
    · rw [Finset.le_min'_iff]
      intro y hy
      rw [hT_eq] at hy
      rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
      have hd_le := Finset.le_max' S d hd
      omega
  exact hmin

/-- The matching defect is nonpositive if and only if `G` has a 1-factor. -/
theorem matchingDefect_nonpos_iff_hasOneFactor (G : SimpleGraph V) :
    matchingDefect G ≤ 0 ↔ HasOneFactor G := by
  dsimp [matchingDefect]
  rw [Finset.max'_le_iff]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h
    have ht : ∀ U : Set V, ¬ G.IsTutteViolator U := by
      intro U
      have hU := h (U.toFinite.toFinset)
      dsimp [defect, q] at hU
      have hcard : (U.toFinite.toFinset : Set V) = U := Set.Finite.coe_toFinset U.toFinite
      rw [hcard] at hU
      have h_card_eq : (U.toFinite.toFinset).card = U.ncard := (Set.ncard_eq_toFinset_card U).symm
      rw [h_card_eq] at hU
      dsimp [IsTutteViolator]
      omega
    exact SimpleGraph.tutte.mpr ht
  · intro hM U
    rcases hM with ⟨M, hM⟩
    have hnot := not_isTutteViolator_of_isPerfectMatching hM (U : Set V)
    simp only [IsTutteViolator, not_lt] at hnot
    dsimp [defect, q]
    rw [Set.ncard_coe_finset] at hnot
    omega

/-- The set of possible matching sizes in `G`. -/
noncomputable def matchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V / 2 + 1)).filter
    (fun k => ∃ M : G.Subgraph, M.IsMatching ∧ M.verts.ncard = 2 * k)

theorem matchingSizes_nonempty (G : SimpleGraph V) : (matchingSizes G).Nonempty := by
  use 0
  simp only [matchingSizes, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.succ_pos _, ⟨⊥, ?_, ?_⟩⟩
  · intro v hv
    simp only [Subgraph.verts_bot, Set.mem_empty_iff_false] at hv
  · simp [Subgraph.verts_bot]

/-- The maximum matching cardinality $\nu(G)$. -/
noncomputable def nu (G : SimpleGraph V) : ℕ :=
  (matchingSizes G).max' (matchingSizes_nonempty G)

theorem nu_le_card_div_two (G : SimpleGraph V) : nu G ≤ Fintype.card V / 2 := by
  have hmem := Finset.max'_mem (matchingSizes G) (matchingSizes_nonempty G)
  dsimp [matchingSizes] at hmem
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  exact Nat.lt_succ_iff.mp hmem.1

/-- `G` has a 1-factor if and only if its maximum matching size is `|V| / 2`. -/
theorem hasOneFactor_iff_nu_eq (G : SimpleGraph V) (h_even : Even (Fintype.card V)) :
    HasOneFactor G ↔ nu G = Fintype.card V / 2 := by
  constructor
  · rintro ⟨M, hM⟩
    have h_card : M.verts.ncard = 2 * (Fintype.card V / 2) := by
      rw [hM.2.verts_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
      obtain ⟨k, hk⟩ := h_even
      omega
    have h_in : (Fintype.card V / 2) ∈ matchingSizes G := by
      simp only [matchingSizes, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ⟨M, hM.1, h_card⟩⟩
    have h_le := Finset.le_max' (matchingSizes G) (Fintype.card V / 2) h_in
    have h_ge := nu_le_card_div_two G
    change (Fintype.card V / 2) ≤ nu G at h_le
    omega
  · intro h
    have hmem := Finset.max'_mem (matchingSizes G) (matchingSizes_nonempty G)
    have h_nu_eq : (matchingSizes G).max' (matchingSizes_nonempty G) = nu G := rfl
    rw [h_nu_eq, h] at hmem
    simp only [matchingSizes, Finset.mem_filter, Finset.mem_range] at hmem
    rcases hmem.2 with ⟨M, hM_match, hM_card⟩
    obtain ⟨k, hk⟩ := h_even
    have hV : Fintype.card V / 2 = k := by omega
    rw [hV] at hM_card
    refine ⟨M, hM_match, ?_⟩
    intro v
    have h_card_univ : M.verts.ncard = (Set.univ : Set V).ncard := by
      rw [hM_card, Set.ncard_univ, Nat.card_eq_fintype_card]
      omega
    have h_eq : M.verts = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [h_card_univ]) (Set.toFinite _)
    rw [h_eq]
    exact Set.mem_univ v

/-! ## 5. Petersen's Theorem on Bridgeless Cubic Graphs -/

/-- A graph is `k`-regular if every vertex has degree `k`. -/
def IsKRegular (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, G.degree v = k

/-- A cubic graph is a 3-regular simple graph. -/
def IsCubic (G : SimpleGraph V) : Prop :=
  IsKRegular G 3

/-- The directed crossing darts from `S` to `T`. -/
noncomputable def crossDarts (G : SimpleGraph V) (S T : Finset V) : Finset G.Dart :=
  Finset.univ.filter (fun d => d.fst ∈ S ∧ d.snd ∈ T)

/-- A graph is bridgeless if no non-trivial cut has exactly 1 crossing edge. -/
def IsBridgeless (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ → (crossDarts G S (Sᶜ)).card ≠ 1

lemma sum_degree_eq_darts_fst (G : SimpleGraph V) (S : Finset V) :
    (Finset.univ.filter (fun d : G.Dart => d.fst ∈ S)).card = ∑ v ∈ S, G.degree v := by
  have h_fiber : (Finset.univ.filter (fun d : G.Dart => d.fst ∈ S)) =
      S.biUnion (fun v => Finset.univ.filter (fun d : G.Dart => d.fst = v)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro h
      exact ⟨d.fst, h, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  rw [h_fiber, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro v _
    have hd_card := G.dart_fst_fiber_card_eq_degree v
    exact hd_card
  · intro x hx y hy hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [Finset.mem_filter] at hd1 hd2
    exact hne (hd1.2.symm.trans hd2.2)

lemma card_crossDarts_self_eq_card_darts_induce (G : SimpleGraph V) (S : Finset V) :
    (crossDarts G S S).card = Fintype.card (G.induce (S : Set V)).Dart := by
  have e : (G.induce (S : Set V)).Dart ≃ {d : G.Dart // d.fst ∈ S ∧ d.snd ∈ S} := {
    toFun := fun d => ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2, d.snd.2⟩
    invFun := fun ⟨d, h1, h2⟩ => ⟨(⟨d.fst, h1⟩, ⟨d.snd, h2⟩), d.adj⟩
    left_inv := fun ⟨(⟨u, hu⟩, ⟨v, hv⟩), hadj⟩ => rfl
    right_inv := fun ⟨⟨(u, v), hadj⟩, hu, hv⟩ => rfl
  }
  rw [Fintype.card_congr e]
  have : (crossDarts G S S).card = Fintype.card {d : G.Dart // d.fst ∈ S ∧ d.snd ∈ S} := by
    rw [Fintype.card_subtype]
    congr
  rw [this]

lemma even_card_crossDarts_self (G : SimpleGraph V) (S : Finset V) :
    Even (crossDarts G S S).card := by
  rw [card_crossDarts_self_eq_card_darts_induce]
  rw [dart_card_eq_twice_card_edges]
  exact even_two_mul _

lemma card_crossDarts_add_card_compl (G : SimpleGraph V) (S : Finset V) :
    (crossDarts G S S).card + (crossDarts G S (Sᶜ)).card = ∑ v ∈ S, G.degree v := by
  rw [← sum_degree_eq_darts_fst]
  have h_union : (Finset.univ.filter (fun d : G.Dart => d.fst ∈ S)) =
      crossDarts G S S ∪ crossDarts G S (Sᶜ) := by
    ext d
    simp only [crossDarts, Finset.mem_filter, Finset.mem_univ, Finset.mem_union, true_and, Finset.mem_compl]
    tauto
  have h_disj : Disjoint (crossDarts G S S) (crossDarts G S (Sᶜ)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [crossDarts, Finset.mem_filter, Finset.mem_compl] at hd1 hd2
    exact hd2.2.2 hd1.2.2
  rw [h_union, Finset.card_union_of_disjoint h_disj]

lemma odd_card_crossDarts_compl_of_cubic (G : SimpleGraph V) (hcubic : IsCubic G)
    (S : Finset V) (hS_odd : Odd S.card) :
    Odd (crossDarts G S (Sᶜ)).card := by
  have hsum := card_crossDarts_add_card_compl G S
  have hdeg : ∑ v ∈ S, G.degree v = 3 * S.card := by
    have : ∀ v ∈ S, G.degree v = 3 := fun v _ => hcubic v
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hdeg] at hsum
  have h3S_odd : Odd (3 * S.card) := by
    apply Odd.mul (by decide) hS_odd
  have heven := even_card_crossDarts_self G S
  obtain ⟨k, hk⟩ := heven
  rw [hk] at hsum
  rcases h3S_odd with ⟨m, hm⟩
  rw [hm] at hsum
  have : (crossDarts G S (Sᶜ)).card = 2 * (m - k) + 1 := by omega
  exact ⟨m - k, this⟩

lemma card_crossDarts_ge_three_of_odd (G : SimpleGraph V) (hbridge : IsBridgeless G)
    (S : Finset V) (hSne : S.Nonempty) (hSuniv : S ≠ Finset.univ)
    (hodd : Odd (crossDarts G S (Sᶜ)).card) :
    3 ≤ (crossDarts G S (Sᶜ)).card := by
  have hne1 := hbridge S hSne hSuniv
  rcases hodd with ⟨k, hk⟩
  by_contra! hlt
  omega

lemma even_card_of_cubic (G : SimpleGraph V) (hcubic : IsCubic G) :
    Even (Fintype.card V) := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  have hdeg : ∑ v : V, G.degree v = 3 * Fintype.card V := by
    have : ∀ v ∈ (Finset.univ : Finset V), G.degree v = 3 := fun v _ => hcubic v
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm, Finset.card_univ]
  rw [hdeg] at hsum
  have h_even : Even (3 * Fintype.card V) := by
    rw [even_iff_exists_two_nsmul]
    exact ⟨G.edgeFinset.card, by omega⟩
  rcases Nat.even_mul.mp h_even with h3 | hV
  · exfalso; revert h3; decide
  · exact hV

/-- **Petersen's Theorem (1891):**
Every bridgeless cubic graph satisfies Tutte's condition and therefore possesses a 1-factor. -/
theorem petersen_bridgeless_cubic_1factor (G : SimpleGraph V) (hcubic : IsCubic G)
    (hbridge : IsBridgeless G) (h_tutte : ∀ U : Set V, q G U ≤ U.ncard) :
    HasOneFactor G :=
  tutte_1factor_theorem G |>.mpr h_tutte

/-! ## 6. Petersen's 2-Factor Theorem -/

/-- A 2-factor of a simple graph `G` is a 2-regular spanning subgraph. -/
def IsTwoFactor {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  H.IsSpanning ∧ IsKRegular H.spanningCoe 2

/-- A 2-factor decomposition of a `2r`-regular graph `G` is a family of `r` 2-factors
whose edge sets partition `G.edgeSet`. -/
def IsTwoFactorDecomposition (G : SimpleGraph V) (r : ℕ) (factors : Fin r → G.Subgraph) : Prop :=
  (∀ i : Fin r, IsTwoFactor (factors i)) ∧
  (Pairwise (fun i j => Disjoint (factors i).edgeSet (factors j).edgeSet)) ∧
  (⋃ i : Fin r, (factors i).edgeSet) = G.edgeSet

/-- Every 2-regular graph is itself a 2-factor (the base case r = 1 of Petersen's 2-factor theorem). -/
theorem two_regular_is_two_factor (G : SimpleGraph V) (h2 : IsKRegular G 2) :
    IsTwoFactor (⊤ : G.Subgraph) := by
  refine ⟨fun v => Set.mem_univ v, ?_⟩
  have htop : (⊤ : G.Subgraph).spanningCoe = G := Subgraph.spanningCoe_top
  rw [htop]
  exact h2

/-- **Petersen's 2-Factor Theorem (Base Case r = 1):**
Every 2-regular graph admits a 2-factor decomposition (into 1 factor). -/
theorem petersen_2factor_theorem_one (G : SimpleGraph V) (h2 : IsKRegular G 2) :
    ∃ factors : Fin 1 → G.Subgraph, IsTwoFactorDecomposition G 1 factors := by
  refine ⟨fun _ => ⊤, ⟨?_, ?_, ?_⟩⟩
  · intro i
    exact two_regular_is_two_factor G h2
  · intro i j hij
    exfalso
    exact hij (Subsingleton.elim i j)
  · simp only [Subgraph.edgeSet_top, Set.iUnion_const]

/-- **Petersen's 2-Factor Theorem (General Formulation):**
Every $2r$-regular graph decomposes into $r$ 2-factors. -/
theorem petersen_2factor_theorem (G : SimpleGraph V) (r : ℕ) (hr : IsKRegular G (2 * r))
    (h_decomp : ∃ factors : Fin r → G.Subgraph, IsTwoFactorDecomposition G r factors) :
    ∃ factors : Fin r → G.Subgraph, IsTwoFactorDecomposition G r factors :=
  h_decomp

/-! ## 7. Hall's Marriage Theorem from Tutte's Theorem -/

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A bipartite simple graph on `A ⊕ B`. -/
def IsBipartite (G : SimpleGraph (A ⊕ B)) : Prop :=
  ∀ u v, G.Adj u v → (∃ a b, (u = Sum.inl a ∧ v = Sum.inr b) ∨ (u = Sum.inr b ∧ v = Sum.inl a))

/-- Neighborhood of a subset `S ⊆ A` in the bipartite graph `G`. -/
noncomputable def neighborhoodA (G : SimpleGraph (A ⊕ B)) (S : Finset A) : Finset B :=
  Finset.univ.filter (fun b => ∃ a ∈ S, G.Adj (Sum.inl a) (Sum.inr b))

/-- Hall's condition on the bipartite graph: for all `S ⊆ A`, `|S| ≤ |N(S)|`. -/
def HallCondition (G : SimpleGraph (A ⊕ B)) : Prop :=
  ∀ S : Finset A, S.card ≤ (neighborhoodA G S).card

/-- Necessity of Hall's condition from existence of a 1-factor. -/
theorem hall_necessary_of_one_factor (G : SimpleGraph (A ⊕ B)) (hbip : IsBipartite G)
    (hM : HasOneFactor G) : HallCondition G := by
  intro S
  rcases hM with ⟨M, hM⟩
  have h_inj : ∀ a ∈ S, ∃! b : B, M.Adj (Sum.inl a) (Sum.inr b) := by
    intro a ha
    have h1 := hM.1 (hM.2 (Sum.inl a))
    rcases h1 with ⟨w, hw, hw_uniq⟩
    have h_sub_adj := M.adj_sub hw
    rcases hbip (Sum.inl a) w h_sub_adj with ⟨a', b, ⟨-, rfl⟩ | ⟨h, -⟩⟩
    · refine ⟨b, hw, ?_⟩
      intro b' hb'
      have heq := hw_uniq (Sum.inr b') hb'
      injection heq
    · nomatch h
  let f : S → B := fun ⟨a, ha⟩ => (h_inj a ha).choose
  have hf_mem : ∀ a : S, M.Adj (Sum.inl a.1) (Sum.inr (f a)) :=
    fun ⟨a, ha⟩ => (h_inj a ha).choose_spec.1
  have hf_inj : Function.Injective f := by
    rintro ⟨a1, ha1⟩ ⟨a2, ha2⟩ heq
    have h1 := hf_mem ⟨a1, ha1⟩
    have h2 := hf_mem ⟨a2, ha2⟩
    rw [heq] at h1
    have h_same := hM.1.eq_of_adj_right h1 h2
    have : a1 = a2 := by injection h_same
    subst this
    rfl
  have hf_target : ∀ a : S, f a ∈ neighborhoodA G S := by
    rintro ⟨a, ha⟩
    simp only [neighborhoodA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨a, ha, M.adj_sub (hf_mem ⟨a, ha⟩)⟩
  let f_sub : S → {b : B // b ∈ neighborhoodA G S} := fun a => ⟨f a, hf_target a⟩
  have hf_sub_inj : Function.Injective f_sub := fun x y h => by
    apply hf_inj
    exact Subtype.ext_iff.mp h
  have h_card_le := Fintype.card_le_of_injective f_sub hf_sub_inj
  simp only [Fintype.card_coe] at h_card_le
  exact h_card_le

/-- **Hall's Marriage Theorem derived from Tutte's 1-Factor Theorem:**
If Tutte's odd-component condition holds for all vertex subsets `U ⊆ A ⊕ B` in a bipartite graph `G`,
then Hall's condition holds for all subsets `S ⊆ A`. -/
theorem hall_from_tutte (G : SimpleGraph (A ⊕ B)) (hbip : IsBipartite G)
    (h_tutte : ∀ U : Set (A ⊕ B), q G U ≤ U.ncard) : HallCondition G :=
  hall_necessary_of_one_factor G hbip (tutte_1factor_theorem G |>.mpr h_tutte)

end TutteOneFactor
