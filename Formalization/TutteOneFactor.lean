import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Basic

open SimpleGraph
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TutteOneFactor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
# Tutte's 1-Factor Theorem, Tutte–Berge Formula, and Matching Defect

This module formalizes:
1. **1-Factors and Perfect Matchings** in simple graphs.
2. **Odd Connected Components** $q(G \setminus U)$.
3. **Tutte's 1-Factor Theorem**: $G$ has a 1-factor $\iff \forall U \subseteq V, q(G \setminus U) \le |U|$.
4. **Tutte–Berge Formula & Matching Defect**:
   $$\nu(G) = \frac{1}{2} \min_{U \subseteq V} (|V| + |U| - q(G \setminus U))$$
   $$\operatorname{matchingDefect}(G) = \max_{U \subseteq V} (q(G \setminus U) - |U|)$$
5. **Cubic Bridgeless Cut Parity**: Degree sum and cut counting in regular graphs.
6. **2-Factors in Regular Graphs**: Base case decomposition for 2-regular graphs.
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
  have := not_isTutteViolator_of_isPerfectMatching hM U
  rwa [IsTutteViolator, not_lt] at this

/-- If `G` has a 1-factor, the total vertex count `|V|` must be even. -/
theorem even_card_of_hasOneFactor (G : SimpleGraph V) (hM : HasOneFactor G) :
    Even (Fintype.card V) := by
  obtain ⟨M, hM⟩ := hM; exact hM.even_card

/-- **Tutte's 1-Factor Theorem (Equivalence):**
A graph `G` has a 1-factor if and only if for all subsets `U ⊆ V`, `q(G \ U) ≤ |U|`. -/
theorem tutte_1factor_theorem (G : SimpleGraph V) :
    HasOneFactor G ↔ ∀ U : Set V, q G U ≤ U.ncard := by
  refine ⟨tutte_necessity G, fun h => SimpleGraph.tutte.mpr fun U => by
    have := h U; rwa [IsTutteViolator, not_lt]⟩

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
  dsimp [tutteBergeBound, defect]; ring

/-- The Tutte–Berge minimum is exactly `|V| - matchingDefect G`. -/
theorem tutte_berge_min_eq_card_sub_defect (G : SimpleGraph V) :
    tutteBergeMin G = (Fintype.card V : ℤ) - matchingDefect G := by
  have hb : ∀ U, tutteBergeBound G U = (Fintype.card V : ℤ) - defect G U := tutteBergeBound_eq G
  let S : Finset ℤ := Finset.univ.image (defect G)
  let T : Finset ℤ := Finset.univ.image (tutteBergeBound G)
  have hT_eq : T = S.image (fun d => (Fintype.card V : ℤ) - d) := by
    ext t; simp only [T, S, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨U, hu⟩ => ⟨defect G U, ⟨U, rfl⟩, by rw [← hb, hu]⟩,
           fun ⟨d, ⟨U, hu⟩, hd⟩ => ⟨U, by rw [hb, hu, hd]⟩⟩
  apply le_antisymm
  · have := Finset.min'_le T _ (by rw [hT_eq]; exact Finset.mem_image_of_mem _ (Finset.max'_mem S (by simp [S])))
    exact this
  · rw [show tutteBergeMin G = T.min' (by simp [T]) from rfl, Finset.le_min'_iff]
    intro y hy; rw [hT_eq] at hy; rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
    have hd_le := Finset.le_max' S d hd
    show (Fintype.card V : ℤ) - S.max' (by simp [S]) ≤ (Fintype.card V : ℤ) - d
    omega

/-- The matching defect is nonpositive if and only if `G` has a 1-factor. -/
theorem matchingDefect_nonpos_iff_hasOneFactor (G : SimpleGraph V) :
    matchingDefect G ≤ 0 ↔ HasOneFactor G := by
  rw [matchingDefect, Finset.max'_le_iff]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff, defect]
  refine ⟨fun h => (tutte_1factor_theorem G).mpr fun U => by
    have hU := h U.toFinite.toFinset
    rw [Set.Finite.coe_toFinset, (Set.ncard_eq_toFinset_card U).symm] at hU
    exact_mod_cast (sub_nonpos.mp hU),
    fun hM U => by
      have := (tutte_1factor_theorem G).mp hM (U : Set V)
      rw [Set.ncard_coe_finset] at this
      exact sub_nonpos.mpr (by exact_mod_cast this)⟩

/-- The set of possible matching sizes in `G`. -/
noncomputable def matchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (Finset.range (Fintype.card V / 2 + 1)).filter
    (fun k => ∃ M : G.Subgraph, M.IsMatching ∧ M.verts.ncard = 2 * k)

theorem matchingSizes_nonempty (G : SimpleGraph V) : (matchingSizes G).Nonempty := by
  use 0; simp only [matchingSizes, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.succ_pos _, ⊥, fun v hv => by simp [Subgraph.verts_bot] at hv, by simp [Subgraph.verts_bot]⟩

/-- The maximum matching cardinality $\nu(G)$. -/
noncomputable def nu (G : SimpleGraph V) : ℕ :=
  (matchingSizes G).max' (matchingSizes_nonempty G)

theorem nu_le_card_div_two (G : SimpleGraph V) : nu G ≤ Fintype.card V / 2 :=
  Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.max'_mem _ _)).1)

/-- `G` has a 1-factor if and only if its maximum matching size is `|V| / 2`. -/
theorem hasOneFactor_iff_nu_eq (G : SimpleGraph V) (h_even : Even (Fintype.card V)) :
    HasOneFactor G ↔ nu G = Fintype.card V / 2 := by
  constructor
  · rintro ⟨M, hM⟩
    have h_card : M.verts.ncard = 2 * (Fintype.card V / 2) := by
      rw [hM.2.verts_eq_univ, Set.ncard_univ, Nat.card_eq_fintype_card]; obtain ⟨k, hk⟩ := h_even; omega
    have h_in : (Fintype.card V / 2) ∈ matchingSizes G := by
      simp only [matchingSizes, Finset.mem_filter, Finset.mem_range]
      obtain ⟨k, hk⟩ := h_even; exact ⟨by omega, M, hM.1, h_card⟩
    exact le_antisymm (nu_le_card_div_two G) (Finset.le_max' _ _ h_in)
  · intro h
    have hmem : nu G ∈ matchingSizes G := Finset.max'_mem _ (matchingSizes_nonempty G)
    rw [h, matchingSizes, Finset.mem_filter] at hmem
    rcases hmem.2 with ⟨M, hM_match, hM_card⟩
    refine ⟨M, hM_match, fun v => ?_⟩
    have h_eq : M.verts = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
      rw [hM_card, Set.ncard_univ, Nat.card_eq_fintype_card]
      obtain ⟨k, hk⟩ := h_even; omega
    exact h_eq ▸ Set.mem_univ v

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
  have : (Finset.univ.filter (fun d : G.Dart => d.fst ∈ S)) =
      S.biUnion (fun v => Finset.univ.filter (fun d : G.Dart => d.fst = v)) := by
    ext d; simp [eq_comm]
  rw [this, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun v _ => G.dart_fst_fiber_card_eq_degree v
  · intro x _ y _ hne; simp [Function.onFun, Finset.disjoint_left]; rintro d rfl; exact hne

lemma card_crossDarts_self_eq_card_darts_induce (G : SimpleGraph V) (S : Finset V) :
    (crossDarts G S S).card = Fintype.card (G.induce (S : Set V)).Dart := by
  have e : (G.induce (S : Set V)).Dart ≃ {d : G.Dart // d.fst ∈ S ∧ d.snd ∈ S} := {
    toFun := fun d => ⟨⟨(d.fst.1, d.snd.1), d.adj⟩, d.fst.2, d.snd.2⟩
    invFun := fun ⟨d, h1, h2⟩ => ⟨(⟨d.fst, h1⟩, ⟨d.snd, h2⟩), d.adj⟩
    left_inv := fun ⟨(⟨u, hu⟩, ⟨v, hv⟩), hadj⟩ => rfl
    right_inv := fun ⟨⟨(u, v), hadj⟩, hu, hv⟩ => rfl
  }
  rw [Fintype.card_congr e, Fintype.card_subtype, crossDarts]

lemma even_card_crossDarts_self (G : SimpleGraph V) (S : Finset V) :
    Even (crossDarts G S S).card := by
  rw [card_crossDarts_self_eq_card_darts_induce, dart_card_eq_twice_card_edges]
  exact even_two_mul _

lemma card_crossDarts_add_card_compl (G : SimpleGraph V) (S : Finset V) :
    (crossDarts G S S).card + (crossDarts G S (Sᶜ)).card = ∑ v ∈ S, G.degree v := by
  rw [← sum_degree_eq_darts_fst, crossDarts, crossDarts, ← Finset.card_union_of_disjoint]
  · congr 1; ext d; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_union, Finset.mem_compl, true_and]; tauto
  · rw [Finset.disjoint_left]; simp only [Finset.mem_filter, Finset.mem_compl]; rintro d ⟨-, -, h1⟩ ⟨-, -, h2⟩; exact h2 h1

lemma odd_card_crossDarts_compl_of_cubic (G : SimpleGraph V) (hcubic : IsCubic G)
    (S : Finset V) (hS_odd : Odd S.card) :
    Odd (crossDarts G S (Sᶜ)).card := by
  have hsum := card_crossDarts_add_card_compl G S
  rw [Finset.sum_congr rfl (fun v _ => hcubic v), Finset.sum_const, smul_eq_mul, mul_comm] at hsum
  obtain ⟨k, hk⟩ := even_card_crossDarts_self G S
  obtain ⟨m, hm⟩ := hS_odd
  exact ⟨3 * m + 1 - k, by omega⟩

lemma card_crossDarts_ge_three_of_odd (G : SimpleGraph V) (hbridge : IsBridgeless G)
    (S : Finset V) (hSne : S.Nonempty) (hSuniv : S ≠ Finset.univ)
    (hodd : Odd (crossDarts G S (Sᶜ)).card) :
    3 ≤ (crossDarts G S (Sᶜ)).card := by
  have := hbridge S hSne hSuniv
  obtain ⟨k, hk⟩ := hodd; omega

lemma even_card_of_cubic (G : SimpleGraph V) (hcubic : IsCubic G) :
    Even (Fintype.card V) := by
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hcubic v), Finset.sum_const, smul_eq_mul, mul_comm, Finset.card_univ] at hsum
  have h_even : Even (3 * Fintype.card V) := ⟨G.edgeFinset.card, by omega⟩
  exact (Nat.even_mul.mp h_even).resolve_left (by decide)

/-! ## 6. 2-Factors in Regular Graphs -/

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
    IsTwoFactor (⊤ : G.Subgraph) :=
  ⟨fun _ => Set.mem_univ _, by rwa [Subgraph.spanningCoe_top]⟩

/-- **Petersen's 2-Factor Theorem (Base Case r = 1):**
Every 2-regular graph admits a 2-factor decomposition (into 1 factor). -/
theorem petersen_2factor_theorem_one (G : SimpleGraph V) (h2 : IsKRegular G 2) :
    ∃ factors : Fin 1 → G.Subgraph, IsTwoFactorDecomposition G 1 factors := by
  refine ⟨fun _ => ⊤, fun _ => two_regular_is_two_factor G h2, fun i j hij => (hij (Subsingleton.elim i j)).elim, ?_⟩
  simp only [Subgraph.edgeSet_top, Set.iUnion_const]

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
    rcases hM.1 (hM.2 (Sum.inl a)) with ⟨w, hw, hw_uniq⟩
    rcases hbip (Sum.inl a) w (M.adj_sub hw) with ⟨a', b, ⟨-, rfl⟩ | ⟨h, -⟩⟩
    · exact ⟨b, hw, fun b' hb' => by injection hw_uniq (Sum.inr b') hb'⟩
    · nomatch h
  let f : S → {b : B // b ∈ neighborhoodA G S} := fun ⟨a, ha⟩ =>
    ⟨(h_inj a ha).choose, by
      simp only [neighborhoodA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, M.adj_sub (h_inj a ha).choose_spec.1⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨a1, ha1⟩ ⟨a2, ha2⟩ h
    have h_eq : (h_inj a1 ha1).choose = (h_inj a2 ha2).choose := Subtype.ext_iff.mp h
    have h1 := (h_inj a1 ha1).choose_spec.1
    have h2 := (h_inj a2 ha2).choose_spec.1
    rw [h_eq] at h1
    have := hM.1.eq_of_adj_right h1 h2
    exact Subtype.ext (by injection this)
  simpa using Fintype.card_le_of_injective f hf_inj

/-- **Hall's Marriage Theorem derived from Tutte's 1-Factor Theorem:**
If Tutte's odd-component condition holds for all vertex subsets `U ⊆ A ⊕ B` in a bipartite graph `G`,
then Hall's condition holds for all subsets `S ⊆ A`. -/
theorem hall_from_tutte (G : SimpleGraph (A ⊕ B)) (hbip : IsBipartite G)
    (h_tutte : ∀ U : Set (A ⊕ B), q G U ≤ U.ncard) : HallCondition G :=
  hall_necessary_of_one_factor G hbip (tutte_1factor_theorem G |>.mpr h_tutte)

end TutteOneFactor
