import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity

open Finset

/-!
# General n-Dimensional Sperner's Lemma & Fixed-Point Combinatorics

This module formalizes the general **$n$-Dimensional Sperner's Lemma** (Emanuel Sperner, 1928)
on abstract $n$-dimensional pseudomanifolds with boundary, along with its fixed-point
combinatorics and dimensional specializations (1D, 2D, 3D).

## References
* Sperner, E. (1928). *Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes*.
  Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg, 6(1), 265–272.
* Kuhn, H. W. (1968). *Simplicial Approximation of Fixed Points*.
  Proceedings of the National Academy of Sciences, 61(4), 1238–1242.
-/

namespace SpernerND

variable {α : Type*} [DecidableEq α] {n : ℕ}

-- ============================================================================
-- Section 1: Abstract n-Dimensional Pseudomanifolds with Boundary
-- ============================================================================

/-- An abstract $n$-dimensional pseudomanifold with boundary on vertex type `α`.
    `topSimplices` is a finite family of $(n+1)$-element subsets of `α`.
    Every $n$-element facet (an $n$-element subset of a top simplex) is contained
    in either exactly 1 top simplex (boundary) or exactly 2 top simplices (interior). -/
structure PseudomanifoldND (α : Type*) [DecidableEq α] (n : ℕ) where
  topSimplices : Finset (Finset α)
  top_card : ∀ t ∈ topSimplices, t.card = n + 1
  incident_card : ∀ f ∈ topSimplices.biUnion (fun t => t.powerset.filter (fun s => s.card = n)),
    (topSimplices.filter (fun t => f ⊆ t)).card = 1 ∨ (topSimplices.filter (fun t => f ⊆ t)).card = 2

/-- All $n$-element facets ($(n-1)$-simplices) of an $n$-dimensional pseudomanifold. -/
def PseudomanifoldND.facets (M : PseudomanifoldND α n) : Finset (Finset α) :=
  M.topSimplices.biUnion (fun t => t.powerset.filter (fun s => s.card = n))

/-- The top simplices containing a given facet `f`. -/
def PseudomanifoldND.incidentSimplices (M : PseudomanifoldND α n) (f : Finset α) : Finset (Finset α) :=
  M.topSimplices.filter (fun t => f ⊆ t)

/-- Boundary facets: $n$-element facets contained in exactly 1 top simplex. -/
def PseudomanifoldND.boundaryFacets (M : PseudomanifoldND α n) : Finset (Finset α) :=
  M.facets.filter (fun f => (M.incidentSimplices f).card = 1)

/-- Interior facets: $n$-element facets contained in exactly 2 top simplices. -/
def PseudomanifoldND.interiorFacets (M : PseudomanifoldND α n) : Finset (Finset α) :=
  M.facets.filter (fun f => (M.incidentSimplices f).card = 2)

-- ============================================================================
-- Section 2: Colorings, Doors, and Panchromatic Simplices
-- ============================================================================

/-- An $n$-element facet `f` is a door if its vertices map bijectively onto the first $n$ colors
    $\{0, 1, \dots, n-1\} = \text{univ} \setminus \{\text{Fin.last } n\}$. -/
def isDoor (c : α → Fin (n + 1)) (f : Finset α) : Prop :=
  f.card = n ∧ f.image c = (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n)

instance instDecidableIsDoor (c : α → Fin (n + 1)) (f : Finset α) : Decidable (isDoor c f) :=
  inferInstanceAs (Decidable (f.card = n ∧ f.image c = Finset.univ.erase (Fin.last n)))

/-- An $(n+1)$-element top simplex `t` is panchromatic (fully labeled) if its vertices
    take all $n+1$ colors $\{0, 1, \dots, n\}$. -/
def isPanchromatic (c : α → Fin (n + 1)) (t : Finset α) : Prop :=
  t.card = n + 1 ∧ t.image c = (Finset.univ : Finset (Fin (n + 1)))

instance instDecidableIsPanchromatic (c : α → Fin (n + 1)) (t : Finset α) : Decidable (isPanchromatic c t) :=
  inferInstanceAs (Decidable (t.card = n + 1 ∧ t.image c = Finset.univ))

/-- The collection of $(n-1)$-doors on the boundary of an $(n+1)$-simplex `t`. -/
def simplexDoors (c : α → Fin (n + 1)) (t : Finset α) : Finset (Finset α) :=
  t.powerset.filter (fun f => f.card = n ∧ isDoor c f)

/-- Number of $(n-1)$-doors on an $(n+1)$-simplex `t`. -/
def simplexDoorCount (c : α → Fin (n + 1)) (t : Finset α) : ℕ :=
  (simplexDoors c t).card

-- ============================================================================
-- Section 3: Local Door Count Parity Invariant
-- ============================================================================

lemma eq_erase_of_subset_card_diff_one {t s : Finset α} {v : α}
    (hsub : s ⊆ t) (hv : t \ s = {v}) : s = t.erase v := by
  rw [erase_eq, ← hv, Finset.sdiff_sdiff_eq_self hsub]

lemma powerset_filter_card_eq_image_erase {t : Finset α} {k : ℕ} (ht : t.card = k + 1) :
    t.powerset.filter (fun s => s.card = k) = t.image (fun v => t.erase v) := by
  ext s; simp only [mem_filter, mem_powerset, mem_image]
  refine ⟨fun ⟨hsub, hc⟩ => ?_, fun ⟨v, hvt, heq⟩ => ?_⟩
  · obtain ⟨v, hv⟩ := card_eq_one.mp (by rw [card_sdiff_of_subset hsub, ht, hc, Nat.add_sub_cancel_left])
    exact ⟨v, (mem_sdiff.mp (hv ▸ mem_singleton_self v)).1, (eq_erase_of_subset_card_diff_one hsub hv).symm⟩
  · rw [← heq]; exact ⟨erase_subset v t, by rw [card_erase_of_mem hvt, ht, Nat.add_sub_cancel]⟩

lemma simplexDoors_eq_image_filter (c : α → Fin (n + 1)) {t : Finset α} (ht : t.card = n + 1) :
    simplexDoors c t = (t.filter (fun v => isDoor c (t.erase v))).image (fun v => t.erase v) := by
  ext s; simp only [simplexDoors, mem_filter, mem_powerset, mem_image]
  constructor
  · rintro ⟨hsub, hc, hd⟩
    have : s ∈ t.powerset.filter (·.card = n) := mem_filter.mpr ⟨mem_powerset.mpr hsub, hc⟩
    rw [powerset_filter_card_eq_image_erase ht, mem_image] at this
    obtain ⟨v, hvt, rfl⟩ := this
    exact ⟨v, ⟨hvt, hd⟩, rfl⟩
  · rintro ⟨v, ⟨hvt, hd⟩, rfl⟩
    exact ⟨erase_subset v t, by rw [card_erase_of_mem hvt, ht, Nat.add_sub_cancel], hd⟩

lemma simplexDoorCount_eq_card_filter (c : α → Fin (n + 1)) {t : Finset α} (ht : t.card = n + 1) :
    simplexDoorCount c t = (t.filter (fun v => isDoor c (t.erase v))).card := by
  rw [simplexDoorCount, simplexDoors_eq_image_filter c ht, card_image_of_injOn]
  intro u hu v hv; exact erase_injOn t (mem_filter.mp hu).1 (mem_filter.mp hv).1

lemma image_erase_of_injOn {β : Type*} [DecidableEq β] {s : Finset α} {f : α → β}
    (hinj : Set.InjOn f s) {a : α} (ha : a ∈ s) :
    (s.erase a).image f = (s.image f).erase (f a) := by
  ext b; simp only [mem_image, mem_erase]
  refine ⟨fun ⟨x, ⟨hx, hxs⟩, heq⟩ => ⟨fun hb => hx (hinj hxs ha (heq.trans hb)), x, hxs, heq⟩,
          fun ⟨hb, x, hxs, heq⟩ => ⟨x, ⟨fun h => hb (h ▸ heq.symm), hxs⟩, heq⟩⟩

lemma card_filter_door_of_panchromatic (c : α → Fin (n + 1)) {t : Finset α} (ht : t.card = n + 1)
    (h_pan : isPanchromatic c t) :
    (t.filter (fun v => isDoor c (t.erase v))).card = 1 := by
  have hinj : Set.InjOn c (t : Set α) := by
    rw [← card_image_iff, h_pan.2, card_univ, Fintype.card_fin, ht]
  obtain ⟨v_last, hv_last_t, hc_last⟩ := mem_image.mp (by rw [h_pan.2]; exact mem_univ (Fin.last n))
  have h_eq : t.filter (fun v => isDoor c (t.erase v)) = {v_last} := by
    ext v; simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hvt, hd⟩
      by_contra hne
      have : Fin.last n ∈ (t.erase v).image c := by
        rw [image_erase_of_injOn hinj hvt, h_pan.2, mem_erase]
        exact ⟨fun h => hne (hinj hv_last_t hvt (hc_last.trans h)).symm, mem_univ _⟩
      rw [hd.2] at this
      exact (mem_erase.mp this).1 rfl
    · rintro rfl
      refine ⟨hv_last_t, by rw [card_erase_of_mem hv_last_t, ht, Nat.add_sub_cancel], ?_⟩
      rw [image_erase_of_injOn hinj hv_last_t, h_pan.2, hc_last]
  rw [h_eq, card_singleton]

lemma card_filter_door_of_not_panchromatic (c : α → Fin (n + 1)) {t : Finset α} (ht : t.card = n + 1)
    (h_not_pan : ¬ isPanchromatic c t) :
    (t.filter (fun v => isDoor c (t.erase v))).card = 0 ∨
    (t.filter (fun v => isDoor c (t.erase v))).card = 2 := by
  by_cases h0 : (t.filter (fun v => isDoor c (t.erase v))).card = 0
  · exact Or.inl h0
  · right
    obtain ⟨v1, hv1_filter⟩ := card_pos.mp (Nat.pos_of_ne_zero h0)
    have hv1_t : v1 ∈ t := (mem_filter.mp hv1_filter).1
    have hv1_door : isDoor c (t.erase v1) := (mem_filter.mp hv1_filter).2
    have hc_v1_ne : c v1 ≠ Fin.last n := by
      intro hlast; refine h_not_pan ⟨ht, ?_⟩
      have : t.image c = insert (c v1) ((t.erase v1).image c) := by rw [← image_insert, insert_erase hv1_t]
      rw [this, hv1_door.2, hlast, insert_erase (mem_univ _)]
    have h_im_t : t.image c = (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n) := by
      have : t.image c = insert (c v1) ((t.erase v1).image c) := by rw [← image_insert, insert_erase hv1_t]
      rw [this, hv1_door.2, insert_eq_of_mem (mem_erase.mpr ⟨hc_v1_ne, mem_univ _⟩)]
    have hc_v1_in : c v1 ∈ (t.erase v1).image c := by rw [hv1_door.2, mem_erase]; exact ⟨hc_v1_ne, mem_univ _⟩
    obtain ⟨v2, hv2_erase, hc_v2_eq⟩ := mem_image.mp hc_v1_in
    have hv2_ne : v2 ≠ v1 := (mem_erase.mp hv2_erase).1
    have hv2_t : v2 ∈ t := (mem_erase.mp hv2_erase).2
    have hinj1 : Set.InjOn c (t.erase v1 : Set α) := by
      rw [← card_image_iff, hv1_door.2, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
          card_erase_of_mem hv1_t, ht]
    have h_eq_pair : t.filter (fun v => isDoor c (t.erase v)) = {v1, v2} := by
      ext y; simp only [mem_filter, mem_insert, mem_singleton]
      refine ⟨fun ⟨hyt, hd⟩ => ?_, fun hy => ?_⟩
      · by_contra! hne
        have hye1 : y ∈ t.erase v1 := mem_erase.mpr ⟨hne.1, hyt⟩
        have hcy_ne_c2 : c y ≠ c v2 := fun h => hne.2 (hinj1 hye1 hv2_erase h)
        have hcy_not : c y ∉ (t.erase y).image c := by
          intro hc_in
          obtain ⟨x, hx_erase, hcx⟩ := mem_image.mp hc_in
          obtain ⟨hxy, hxt⟩ := mem_erase.mp hx_erase
          by_cases hxv1 : x = v1
          · exact hcy_ne_c2 (hcx.symm.trans (hxv1 ▸ hc_v2_eq.symm))
          · exact hxy (hinj1 (mem_erase.mpr ⟨hxv1, hxt⟩) hye1 hcx)
        rw [hd.2, ← h_im_t] at hcy_not
        exact hcy_not (mem_image_of_mem c hyt)
      · rcases hy with hy1 | hy2
        · rw [hy1]; exact ⟨hv1_t, hv1_door⟩
        · rw [hy2]; refine ⟨hv2_t, by rw [card_erase_of_mem hv2_t, ht, Nat.add_sub_cancel], ?_⟩
          ext k; simp only [mem_image, mem_erase, mem_univ, and_true]
          refine ⟨fun ⟨x, ⟨hxv2, hxt⟩, heq⟩ => by
                    have : c x ∈ t.image c := mem_image_of_mem c hxt
                    rw [h_im_t, mem_erase] at this; exact heq ▸ this.1,
                  fun hk => ?_⟩
          obtain ⟨x, hx1, rfl⟩ := mem_image.mp (by rw [hv1_door.2, mem_erase]; exact ⟨hk, mem_univ _⟩)
          by_cases hx2 : x = v2
          · exact ⟨v1, ⟨hv2_ne.symm, hv1_t⟩, hx2 ▸ hc_v2_eq.symm⟩
          · exact ⟨x, ⟨hx2, (mem_erase.mp hx1).2⟩, rfl⟩
    rw [h_eq_pair, card_pair hv2_ne.symm]

/-- **Local Door Count Invariant:**
    The door count of any $(n+1)$-element simplex modulo 2 is 1 if and only if
    the simplex is panchromatic. -/
theorem simplexDoorCount_mod_two (c : α → Fin (n + 1)) (t : Finset α) (ht : t.card = n + 1) :
    simplexDoorCount c t % 2 = if isPanchromatic c t then 1 else 0 := by
  rw [simplexDoorCount_eq_card_filter c ht]
  split_ifs with h_pan
  · rw [card_filter_door_of_panchromatic c ht h_pan]
  · rcases card_filter_door_of_not_panchromatic c ht h_pan with h | h <;> rw [h]

-- ============================================================================
-- Section 4: Global Double-Counting Relation
-- ============================================================================

lemma sum_mod_two_eq_nd {β : Type*} [DecidableEq β] (s : Finset β) (f : β → ℕ) (p : β → Prop) [DecidablePred p]
    (h_mod : ∀ x ∈ s, f x % 2 = if p x then 1 else 0) :
    (∑ x ∈ s, f x) % 2 = (s.filter p).card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [sum_insert has, filter_insert]
    have ha := h_mod a (mem_insert_self a s)
    have ih_s := ih (fun t ht => h_mod t (mem_insert_of_mem ht))
    rw [Nat.add_mod, ha, ih_s]
    split_ifs with hp
    · rw [card_insert_of_notMem (fun h => has (mem_filter.mp h).1)]; omega
    · rw [zero_add, Nat.mod_mod]

lemma card_filter_eq_sum_ite {β : Type*} [DecidableEq β] (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  rw [card_eq_sum_ones, sum_filter]

lemma sum_boundary_eq_nd (M : PseudomanifoldND α n) (c : α → Fin (n + 1)) :
    (∑ f ∈ M.boundaryFacets, if isDoor c f then (M.incidentSimplices f).card else 0) =
    (M.boundaryFacets.filter (isDoor c)).card := by
  rw [card_filter_eq_sum_ite]
  exact Finset.sum_congr rfl (fun f hf => by rw [(mem_filter.mp hf).2])

lemma sum_interior_eq_nd (M : PseudomanifoldND α n) (c : α → Fin (n + 1)) :
    (∑ f ∈ M.interiorFacets, if isDoor c f then (M.incidentSimplices f).card else 0) =
    2 * (M.interiorFacets.filter (isDoor c)).card := by
  rw [card_filter_eq_sum_ite, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun f hf => by rw [(mem_filter.mp hf).2]; split_ifs <;> omega)

/-- Double-counting identity: summing door counts across all top simplices equals
    boundary doors plus twice interior doors. -/
theorem double_counting_sum_eq_nd (M : PseudomanifoldND α n) (c : α → Fin (n + 1)) :
    (∑ t ∈ M.topSimplices, simplexDoorCount c t) =
    (M.boundaryFacets.filter (isDoor c)).card + 2 * (M.interiorFacets.filter (isDoor c)).card := by
  have h_door_sum (t : Finset α) (ht : t ∈ M.topSimplices) :
      simplexDoorCount c t = ∑ f ∈ M.facets, if f ⊆ t ∧ isDoor c f then 1 else 0 := by
    dsimp [simplexDoorCount, simplexDoors]
    have : (t.powerset.filter (fun s => s.card = n ∧ isDoor c s)) =
        (M.facets.filter (fun f => f ⊆ t ∧ isDoor c f)) := by
      ext f; simp only [mem_filter, mem_powerset]
      refine ⟨fun ⟨hsub, hc, hd⟩ => ⟨mem_biUnion.mpr ⟨t, ht, mem_filter.mpr ⟨mem_powerset.mpr hsub, hc⟩⟩, hsub, hd⟩,
              fun ⟨_, hsub, hd⟩ => ⟨hsub, hd.1, hd⟩⟩
    rw [this, card_filter_eq_sum_ite]
  have h_facet_term (f : Finset α) :
      (∑ t ∈ M.topSimplices, if f ⊆ t ∧ isDoor c f then 1 else 0) =
      if isDoor c f then (M.incidentSimplices f).card else 0 := by
    dsimp [PseudomanifoldND.incidentSimplices]
    split_ifs with hd
    · have : (∑ t ∈ M.topSimplices, if f ⊆ t ∧ isDoor c f then 1 else 0) =
          ∑ t ∈ M.topSimplices, if f ⊆ t then 1 else 0 := Finset.sum_congr rfl (fun t _ => by simp [hd])
      rw [this, ← card_filter_eq_sum_ite]
    · exact Finset.sum_eq_zero (fun t _ => by simp [hd])
  have h_union : M.facets = M.boundaryFacets ∪ M.interiorFacets := by
    ext f; simp only [PseudomanifoldND.facets, PseudomanifoldND.boundaryFacets, PseudomanifoldND.interiorFacets,
      mem_union, mem_filter]
    exact ⟨fun hf => (M.incident_card f hf).elim (Or.inl ⟨hf, ·⟩) (Or.inr ⟨hf, ·⟩), fun h => h.elim (·.1) (·.1)⟩
  have h_disj : Disjoint M.boundaryFacets M.interiorFacets := by
    rw [PseudomanifoldND.boundaryFacets, PseudomanifoldND.interiorFacets, disjoint_filter]; intro _ _ h1 h2; omega
  rw [Finset.sum_congr rfl h_door_sum, Finset.sum_comm, Finset.sum_congr rfl (fun f _ => h_facet_term f),
      h_union, sum_union h_disj, sum_boundary_eq_nd, sum_interior_eq_nd]

-- ============================================================================
-- Section 5: Main n-Dimensional Sperner Theorems
-- ============================================================================

/-- **General n-Dimensional Sperner Parity Theorem (Sperner, 1928):**
    The number of panchromatic $(n+1)$-simplices in any $n$-dimensional pseudomanifold
    with boundary has the same parity modulo 2 as the number of $(n-1)$-doors on its boundary. -/
theorem sperner_nd_parity (M : PseudomanifoldND α n) (c : α → Fin (n + 1)) :
    (M.topSimplices.filter (isPanchromatic c)).card % 2 =
    (M.boundaryFacets.filter (isDoor c)).card % 2 := by
  have h_left : (∑ t ∈ M.topSimplices, simplexDoorCount c t) % 2 =
      (M.topSimplices.filter (isPanchromatic c)).card % 2 :=
    sum_mod_two_eq_nd _ _ _ (fun t ht => simplexDoorCount_mod_two c t (M.top_card t ht))
  have h_right : (∑ t ∈ M.topSimplices, simplexDoorCount c t) % 2 =
      (M.boundaryFacets.filter (isDoor c)).card % 2 := by
    rw [double_counting_sum_eq_nd, Nat.add_mod]; omega
  rw [← h_left, h_right]

/-- **General n-Dimensional Sperner's Lemma (Parity Form):**
    If the boundary contains an odd number of $(n-1)$-doors, the number of panchromatic
    $(n+1)$-simplices is odd. -/
theorem sperner_nd_odd (M : PseudomanifoldND α n) (c : α → Fin (n + 1))
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    Odd (M.topSimplices.filter (isPanchromatic c)).card := by
  rwa [Nat.odd_iff, sperner_nd_parity, ← Nat.odd_iff]

/-- **General n-Dimensional Sperner Existence Theorem:**
    Whenever the boundary of an $n$-dimensional pseudomanifold contains an odd number of
    $(n-1)$-doors, there exists at least one panchromatic $(n+1)$-simplex (taking all $n+1$ colors). -/
theorem sperner_nd_exists (M : PseudomanifoldND α n) (c : α → Fin (n + 1))
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    ∃ t ∈ M.topSimplices, isPanchromatic c t := by
  obtain ⟨k, hk⟩ := sperner_nd_odd M c h_bd
  have hpos : 0 < (M.topSimplices.filter (isPanchromatic c)).card := by omega
  obtain ⟨t, ht, hp⟩ := filter_nonempty_iff.mp (card_pos.mp hpos)
  exact ⟨t, ht, hp⟩

-- ============================================================================
-- Section 6: Dimensional Specializations (1D, 2D, 3D)
-- ============================================================================

/-- 1D Specialization of Sperner's Parity Theorem ($n = 1$). -/
theorem sperner_1d_parity_nd (M : PseudomanifoldND α 1) (c : α → Fin 2) :
    (M.topSimplices.filter (isPanchromatic c)).card % 2 =
    (M.boundaryFacets.filter (isDoor c)).card % 2 := sperner_nd_parity M c

/-- 1D Specialization of Sperner Existence Theorem ($n = 1$). -/
theorem sperner_1d_exists_nd (M : PseudomanifoldND α 1) (c : α → Fin 2)
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    ∃ t ∈ M.topSimplices, isPanchromatic c t := sperner_nd_exists M c h_bd

/-- 2D Specialization of Sperner's Parity Theorem ($n = 2$). -/
theorem sperner_2d_parity_nd (M : PseudomanifoldND α 2) (c : α → Fin 3) :
    (M.topSimplices.filter (isPanchromatic c)).card % 2 =
    (M.boundaryFacets.filter (isDoor c)).card % 2 := sperner_nd_parity M c

/-- 2D Specialization of Sperner Existence Theorem ($n = 2$). -/
theorem sperner_2d_exists_nd (M : PseudomanifoldND α 2) (c : α → Fin 3)
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    ∃ t ∈ M.topSimplices, isPanchromatic c t := sperner_nd_exists M c h_bd

/-- 3D Specialization of Sperner's Parity Theorem ($n = 3$). -/
theorem sperner_3d_parity_nd (M : PseudomanifoldND α 3) (c : α → Fin 4) :
    (M.topSimplices.filter (isPanchromatic c)).card % 2 =
    (M.boundaryFacets.filter (isDoor c)).card % 2 := sperner_nd_parity M c

/-- 3D Specialization of Sperner Existence Theorem ($n = 3$). -/
theorem sperner_3d_exists_nd (M : PseudomanifoldND α 3) (c : α → Fin 4)
    (h_bd : Odd (M.boundaryFacets.filter (isDoor c)).card) :
    ∃ t ∈ M.topSimplices, isPanchromatic c t := sperner_nd_exists M c h_bd

end SpernerND