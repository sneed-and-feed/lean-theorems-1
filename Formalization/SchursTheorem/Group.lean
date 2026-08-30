import Formalization.SchursTheorem.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# General Group-Theoretic & Algebraic Schur's Theorem

This module formalizes the general group-theoretic and algebraic extensions of **Schur's Theorem**
(Issai Schur, 1916) to arbitrary groups and additive abelian groups.

## Mathematical Context & Overview

Schur's classical theorem states that in any finite coloring of the positive integers, there exists
a monochromatic solution to $x + y = z$. In modern additive combinatorics and algebraic Ramsey theory,
Schur's theorem is understood as a fundamental partition regularity phenomenon holding in any group $G$:

1. **Multiplicative Group Schur Theorem**: For any group $(G, \cdot)$ and any finite subset
   $S \subseteq G$ with $|S| \ge B_r$ (where $B_r = \text{ramseyTriangleBound } r$), every $r$-coloring
   $\chi : G \to \text{Fin } r$ produces distinct elements $u, v, w \in S$ such that
   $x = u^{-1} v$, $y = v^{-1} w$, and $z = u^{-1} w$ are non-identity elements satisfying
   $x \cdot y = z$ and $\chi(x) = \chi(y) = \chi(z)$.

2. **Additive Abelian Group Schur Theorem**: For any additive abelian group $(A, +)$, any finite subset
   $S \subseteq A$ with $|S| \ge B_r$, and any coloring $\chi : A \to \text{Fin } r$, there exist
   distinct $u, v, w \in S$ such that $x = v - u$, $y = w - v$, and $z = w - u$ are non-zero elements
   satisfying $x + y = z$ and $\chi(x) = \chi(y) = \chi(z)$.

3. **Finite Group Partition Regularity & Sum-Free Sets**: For any finite group $G$ with
   $|G| \ge B_r$, in any $r$-partition (or cover) $G \setminus \{1\} = \bigcup_{i=0}^{r-1} C_i$, at least
   one partition class $C_i$ is not product-free (contains $x, y, z \in C_i$ with $x \cdot y = z$).
   Analogously, for any finite additive abelian group $A$, any $r$-partition of $A \setminus \{0\}$
   contains a class that is not sum-free.

## Bound Fidelity Note (Anti-Pattern Q)

Following strict Palomar editorial standards, all docstrings and identifiers explicitly distinguish
between the recursive upper bound $B_r = \text{ramseyTriangleBound } r$ and the exact canonical
extremal Schur / Ramsey numbers $S(r)$ and $R_r(3)$.

## Main Results

* `SchursTheorem.group_schurs_theorem`: Multiplicative Schur theorem for general groups.
* `SchursTheorem.group_schurs_theorem_simple`: Simplified existential form in general groups.
* `SchursTheorem.IsProductFree`: Definition of product-free subsets in groups.
* `SchursTheorem.finite_group_schurs_theorem`: Schur's theorem for finite groups.
* `SchursTheorem.finite_group_color_classes_not_product_free`: Color classes not product-free.
* `SchursTheorem.finite_group_partition_regular`: Partition regularity of $G \setminus \{1\}$.
* `SchursTheorem.addGroup_schurs_theorem`: Schur's theorem for general additive groups.
* `SchursTheorem.addCommGroup_schurs_theorem`: Additive Schur theorem for abelian groups.
* `SchursTheorem.IsSumFree`: Definition of sum-free subsets in additive groups.
* `SchursTheorem.finite_addCommGroup_schurs_theorem`: Additive Schur's theorem for finite abelian groups.
* `SchursTheorem.finite_addCommGroup_partition_regular`: Partition regularity of $A \setminus \{0\}$.
-/

namespace SchursTheorem

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Helper lemma: Any monochromatic triangle in a finite linear order can be sorted
into an ascending chain $a < b < c$ preserving the edge colors. -/
lemma sorted_mono_triangle {n : ℕ} {C : Type*} (edgeColor : Fin n → Fin n → C)
    (h_symm : ∀ u v, edgeColor u v = edgeColor v u)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {col : C}
    (hc_ij : edgeColor i j = col) (hc_ik : edgeColor i k = col) (hc_jk : edgeColor j k = col) :
    ∃ a b c : Fin n, a < b ∧ b < c ∧
      edgeColor a b = col ∧ edgeColor b c = col ∧ edgeColor a c = col := by
  rcases lt_or_gt_of_ne hij with h1 | h1 <;>
  rcases lt_or_gt_of_ne hik with h2 | h2 <;>
  rcases lt_or_gt_of_ne hjk with h3 | h3
  · exact ⟨i, j, k, h1, h3, hc_ij, hc_jk, hc_ik⟩
  · exact ⟨i, k, j, h2, h3, hc_ik, by rwa [h_symm], hc_ij⟩
  · omega
  · exact ⟨k, i, j, h2, h1, by rwa [h_symm], hc_ij, by rwa [h_symm]⟩
  · exact ⟨j, i, k, h1, h2, by rwa [h_symm], hc_ik, hc_jk⟩
  · omega
  · exact ⟨j, k, i, h3, h2, hc_jk, by rwa [h_symm], by rwa [h_symm]⟩
  · exact ⟨k, j, i, h3, h1, by rwa [h_symm], by rwa [h_symm], by rwa [h_symm]⟩

/-! ### 1. Multiplicative Group Schur's Theorem -/

/-- **Group Schur Theorem (Multiplicative Formulation)**:
For any group $G$ (`[Group G] [DecidableEq G]`), any integer $r \ge 1$, any finite subset
$S \subseteq G$ with $|S| \ge \text{ramseyTriangleBound } r$, and any coloring $\chi : G \to \text{Fin } r$,
there exist distinct elements $u, v, w \in S$ such that setting
$x = u^{-1} v$, $y = v^{-1} w$, and $z = u^{-1} w$ satisfies:
* $x \cdot y = z$
* $x \ne 1$, $y \ne 1$, $z \ne 1$
* $\chi(x) = \chi(y) = \chi(z) = c$ for some color $c \in \text{Fin } r$.

Note: `ramseyTriangleBound r` is an explicit recursive upper bound ($B_r$) on the Schur number,
not the exact Ramsey number (Anti-Pattern Q). -/
theorem group_schurs_theorem {G : Type*} [Group G] [DecidableEq G]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset G) (hS : ramseyTriangleBound r ≤ S.card)
    (χ : G → Fin r) :
    ∃ (c : Fin r) (u v w : G) (x y z : G),
      u ∈ S ∧ v ∈ S ∧ w ∈ S ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      x = u⁻¹ * v ∧ y = v⁻¹ * w ∧ z = u⁻¹ * w ∧
      x * y = z ∧
      x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧
      χ x = c ∧ χ y = c ∧ χ z = c := by
  let l := S.toList
  let n := l.length
  have h_ramsey_bound : ramseyTriangleBound r ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]; dsimp [n, l]; rwa [S.length_toList]
  let edgeColor : Fin n → Fin n → Fin r := fun i j =>
    if i < j then χ ((l.get i)⁻¹ * l.get j)
    else if j < i then χ ((l.get j)⁻¹ * l.get i)
    else ⟨0, hr⟩
  have h_edgeColor_symm : ∀ i j, edgeColor i j = edgeColor j i := by
    intro i j
    dsimp [edgeColor]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (asymm h), if_pos h]
    · rfl
    · rw [if_neg (asymm h), if_pos h, if_pos h]
  rcases ramsey_triangle r hr Finset.univ edgeColor h_edgeColor_symm h_ramsey_bound with
    ⟨i, j, k, col, -, -, -, hij, hik, hjk, hc_ij, hc_ik, hc_jk⟩
  rcases sorted_mono_triangle edgeColor h_edgeColor_symm hij hik hjk hc_ij hc_ik hc_jk with
    ⟨a, b, c, hab, hbc, hc_ab, hc_bc, hc_ac⟩
  have hac : a < c := lt_trans hab hbc
  dsimp only [edgeColor] at hc_ab hc_bc hc_ac
  rw [if_pos hab] at hc_ab
  rw [if_pos hbc] at hc_bc
  rw [if_pos hac] at hc_ac
  let u := l.get a; let v := l.get b; let w := l.get c
  have h_nodup := S.nodup_toList
  have huv : u ≠ v := fun h => (ne_of_lt hab) ((List.Nodup.get_inj_iff h_nodup).mp h)
  have huw : u ≠ w := fun h => (ne_of_lt hac) ((List.Nodup.get_inj_iff h_nodup).mp h)
  have hvw : v ≠ w := fun h => (ne_of_lt hbc) ((List.Nodup.get_inj_iff h_nodup).mp h)
  let x := u⁻¹ * v; let y := v⁻¹ * w; let z := u⁻¹ * w
  exact ⟨col, u, v, w, x, y, z,
    Finset.mem_toList.mp (List.get_mem l a),
    Finset.mem_toList.mp (List.get_mem l b),
    Finset.mem_toList.mp (List.get_mem l c),
    huv, huw, hvw, rfl, rfl, rfl,
    by dsimp [x, y, z]; group,
    fun h => huv (inv_mul_eq_one.mp h),
    fun h => hvw (inv_mul_eq_one.mp h),
    fun h => huw (inv_mul_eq_one.mp h),
    hc_ab, hc_bc, hc_ac⟩

/-- **Group Schur Theorem (Existential Elements Corollary)**:
In any $r$-coloring of a group $G$, any finite subset $S \subseteq G$ with
$|S| \ge \text{ramseyTriangleBound } r$ yields non-identity elements $x, y, z \in G \setminus \{1\}$ such that
$x \cdot y = z$ and $\chi(x) = \chi(y) = \chi(z)$. -/
theorem group_schurs_theorem_simple {G : Type*} [Group G] [DecidableEq G]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset G) (hS : ramseyTriangleBound r ≤ S.card)
    (χ : G → Fin r) :
    ∃ (c : Fin r) (x y z : G),
      x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧
      x * y = z ∧
      χ x = c ∧ χ y = c ∧ χ z = c := by
  rcases group_schurs_theorem r hr S hS χ with
    ⟨c, -, -, -, x, y, z, -, -, -, -, -, -, -, -, -, h_prod, hx1, hy1, hz1, hcx, hcy, hcz⟩
  exact ⟨c, x, y, z, hx1, hy1, hz1, h_prod, hcx, hcy, hcz⟩

/-! ### 2. Product-Free Sets and Finite Group Partition Regularity -/

/-- A subset of a group `G` is product-free if it contains no solution to `x * y = z`. -/
def IsProductFree {G : Type*} [Mul G] (s : Finset G) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x * y ∉ s

/-- **Finite Group Schur Theorem**:
For any finite group $G$ with $|G| \ge \text{ramseyTriangleBound } r$, every $r$-coloring
of $G$ contains a monochromatic solution to $x \cdot y = z$ with $x, y, z \ne 1$. -/
theorem finite_group_schurs_theorem {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (r : ℕ) (hr : 1 ≤ r) (hG : ramseyTriangleBound r ≤ Fintype.card G)
    (χ : G → Fin r) :
    ∃ (c : Fin r) (x y z : G),
      x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧
      x * y = z ∧
      χ x = c ∧ χ y = c ∧ χ z = c :=
  group_schurs_theorem_simple r hr Finset.univ (by rwa [Finset.card_univ]) χ

/-- **Finite Group Color Classes Not Product-Free**:
In any $r$-coloring of a finite group $G$ with $|G| \ge \text{ramseyTriangleBound } r$,
at least one color class in $G \setminus \{1\}$ is not product-free. -/
theorem finite_group_color_classes_not_product_free {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (r : ℕ) (hr : 1 ≤ r) (hG : ramseyTriangleBound r ≤ Fintype.card G)
    (χ : G → Fin r) :
    let G_nonunit := (Finset.univ : Finset G).erase 1
    let colorClass (c : Fin r) : Finset G := G_nonunit.filter (fun x => χ x = c)
    ∃ c : Fin r, ¬ IsProductFree (colorClass c) := by
  intro G_nonunit colorClass
  rcases finite_group_schurs_theorem r hr hG χ with ⟨c, x, y, z, hx1, hy1, hz1, hxyz, hcx, hcy, hcz⟩
  have h_in : ∀ {g : G}, g ≠ 1 → χ g = c → g ∈ colorClass c :=
    fun hg hc => Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hg, Finset.mem_univ _⟩, hc⟩
  exact ⟨c, fun h_pf => (hxyz ▸ h_pf x (h_in hx1 hcx) y (h_in hy1 hcy)) (h_in hz1 hcz)⟩

/-- **Finite Group Partition Regularity (Product Formulation)**:
If $G \setminus \{1\}$ is covered by $r$ sets $A_0, \dots, A_{r-1}$ where $|G| \ge \text{ramseyTriangleBound } r$,
then at least one set $A_i$ contains a non-identity solution to $x \cdot y = z$ ($x, y, z \ne 1$). -/
theorem finite_group_partition_regular {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (r : ℕ) (hr : 1 ≤ r) (hG : ramseyTriangleBound r ≤ Fintype.card G)
    (A : Fin r → Finset G)
    (h_cover : (Finset.univ : Finset G).erase 1 ⊆ Finset.biUnion Finset.univ A) :
    ∃ i : Fin r, ∃ x y z, x ∈ A i ∧ y ∈ A i ∧ z ∈ A i ∧ x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y = z := by
  have h_choice : ∀ g : G, ∃ i : Fin r, g ∈ (Finset.univ : Finset G).erase 1 → g ∈ A i := by
    intro g
    by_cases hg : g ∈ (Finset.univ : Finset G).erase 1
    · rcases Finset.mem_biUnion.mp (h_cover hg) with ⟨i, -, hi⟩
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hr⟩, fun h => (hg h).elim⟩
  let χ : G → Fin r := fun g => (h_choice g).choose
  have hχ : ∀ {g : G}, g ≠ 1 → g ∈ A (χ g) :=
    fun hg => (h_choice _).choose_spec (Finset.mem_erase.mpr ⟨hg, Finset.mem_univ _⟩)
  rcases finite_group_schurs_theorem r hr hG χ with ⟨c, x, y, z, hx1, hy1, hz1, hxyz, hcx, hcy, hcz⟩
  exact ⟨c, x, y, z, hcx ▸ hχ hx1, hcy ▸ hχ hy1, hcz ▸ hχ hz1, hx1, hy1, hz1, hxyz⟩

/-- **Finite Group Partition Not Product-Free**:
In any $r$-covering of $G \setminus \{1\}$ with $|G| \ge \text{ramseyTriangleBound } r$,
not all partition classes can be product-free. -/
theorem finite_group_partition_not_product_free {G : Type*} [Fintype G] [Group G] [DecidableEq G]
    (r : ℕ) (hr : 1 ≤ r) (hG : ramseyTriangleBound r ≤ Fintype.card G)
    (A : Fin r → Finset G)
    (h_cover : (Finset.univ : Finset G).erase 1 ⊆ Finset.biUnion Finset.univ A) :
    ∃ i : Fin r, ¬ IsProductFree (A i) := by
  rcases finite_group_partition_regular r hr hG A h_cover with ⟨i, x, y, z, hx, hy, hz, -, -, -, hxyz⟩
  exact ⟨i, fun h_pf => (hxyz ▸ h_pf x hx y hy) hz⟩

/-! ### 3. General Additive Group Schur's Theorem -/

/-- **Additive Group Schur Theorem (General Additive Group)**:
For any additive group $A$ (`[AddGroup A] [DecidableEq A]`), any integer $r \ge 1$,
any finite subset $S \subseteq A$ with $|S| \ge \text{ramseyTriangleBound } r$,
and any coloring $\chi : A \to \text{Fin } r$, there exist distinct elements $u, v, w \in S$
and non-zero elements $x, y, z \in A$ such that:
* $x = -u + v$, $y = -v + w$, $z = -u + w$
* $x + y = z$
* $x \ne 0$, $y \ne 0$, $z \ne 0$
* $\chi(x) = \chi(y) = \chi(z) = c$ for some color $c \in \text{Fin } r$. -/
theorem addGroup_schurs_theorem {A : Type*} [AddGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset A) (hS : ramseyTriangleBound r ≤ S.card)
    (χ : A → Fin r) :
    ∃ (c : Fin r) (u v w : A) (x y z : A),
      u ∈ S ∧ v ∈ S ∧ w ∈ S ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      x = -u + v ∧ y = -v + w ∧ z = -u + w ∧
      x + y = z ∧
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
      χ x = c ∧ χ y = c ∧ χ z = c := by
  let l := S.toList
  let n := l.length
  have h_ramsey_bound : ramseyTriangleBound r ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]; dsimp [n, l]; rwa [S.length_toList]
  let edgeColor : Fin n → Fin n → Fin r := fun i j =>
    if i < j then χ (- l.get i + l.get j)
    else if j < i then χ (- l.get j + l.get i)
    else ⟨0, hr⟩
  have h_edgeColor_symm : ∀ i j, edgeColor i j = edgeColor j i := by
    intro i j
    dsimp [edgeColor]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_pos h, if_neg (asymm h), if_pos h]
    · rfl
    · rw [if_neg (asymm h), if_pos h, if_pos h]
  rcases ramsey_triangle r hr Finset.univ edgeColor h_edgeColor_symm h_ramsey_bound with
    ⟨i, j, k, col, -, -, -, hij, hik, hjk, hc_ij, hc_ik, hc_jk⟩
  rcases sorted_mono_triangle edgeColor h_edgeColor_symm hij hik hjk hc_ij hc_ik hc_jk with
    ⟨a, b, c, hab, hbc, hc_ab, hc_bc, hc_ac⟩
  have hac : a < c := lt_trans hab hbc
  dsimp only [edgeColor] at hc_ab hc_bc hc_ac
  rw [if_pos hab] at hc_ab
  rw [if_pos hbc] at hc_bc
  rw [if_pos hac] at hc_ac
  let u := l.get a; let v := l.get b; let w := l.get c
  have h_nodup := S.nodup_toList
  have huv : u ≠ v := fun h => (ne_of_lt hab) ((List.Nodup.get_inj_iff h_nodup).mp h)
  have huw : u ≠ w := fun h => (ne_of_lt hac) ((List.Nodup.get_inj_iff h_nodup).mp h)
  have hvw : v ≠ w := fun h => (ne_of_lt hbc) ((List.Nodup.get_inj_iff h_nodup).mp h)
  let x := -u + v; let y := -v + w; let z := -u + w
  exact ⟨col, u, v, w, x, y, z,
    Finset.mem_toList.mp (List.get_mem l a),
    Finset.mem_toList.mp (List.get_mem l b),
    Finset.mem_toList.mp (List.get_mem l c),
    huv, huw, hvw, rfl, rfl, rfl,
    by dsimp [x, y, z]; simp [add_assoc],
    fun h => huv (neg_add_eq_zero.mp h),
    fun h => hvw (neg_add_eq_zero.mp h),
    fun h => huw (neg_add_eq_zero.mp h),
    hc_ab, hc_bc, hc_ac⟩

/-! ### 4. Additive Abelian Group Schur's Theorem -/

/-- **Abelian Group Schur Theorem (Additive Formulation)**:
For any additive abelian group $A$ (`[AddCommGroup A] [DecidableEq A]`), any integer $r \ge 1$,
any finite subset $S \subseteq A$ with $|S| \ge \text{ramseyTriangleBound } r$,
and any coloring $\chi : A \to \text{Fin } r$, there exist distinct elements $u, v, w \in S$
and non-zero differences $x = v - u$, $y = w - v$, and $z = w - u$ satisfying:
* $x + y = z$
* $x \ne 0$, $y \ne 0$, $z \ne 0$
* $\chi(x) = \chi(y) = \chi(z) = c$ for some color $c \in \text{Fin } r$. -/
theorem addCommGroup_schurs_theorem {A : Type*} [AddCommGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset A) (hS : ramseyTriangleBound r ≤ S.card)
    (χ : A → Fin r) :
    ∃ (c : Fin r) (u v w : A) (x y z : A),
      u ∈ S ∧ v ∈ S ∧ w ∈ S ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      x = v - u ∧ y = w - v ∧ z = w - u ∧
      x + y = z ∧
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
      χ x = c ∧ χ y = c ∧ χ z = c := by
  rcases addGroup_schurs_theorem r hr S hS χ with
    ⟨c, u, v, w, x, y, z, hu, hv, hw, huv, huw, hvw,
      rfl, rfl, rfl, h_sum, hx0, hy0, hz0, hcx, hcy, hcz⟩
  simp only [neg_add_eq_sub] at h_sum hx0 hy0 hz0 hcx hcy hcz
  exact ⟨c, u, v, w, v - u, w - v, w - u, hu, hv, hw, huv, huw, hvw,
    rfl, rfl, rfl, h_sum, hx0, hy0, hz0, hcx, hcy, hcz⟩

/-- **Abelian Group Schur Theorem (Simple Existential Formulation)**:
In any $r$-coloring of an additive abelian group $A$, any finite subset $S \subseteq A$ with
$|S| \ge \text{ramseyTriangleBound } r$ yields non-zero elements $x, y, z \in A \setminus \{0\}$ such that
$x + y = z$ and $\chi(x) = \chi(y) = \chi(z)$. -/
theorem addCommGroup_schurs_theorem_simple {A : Type*} [AddCommGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (S : Finset A) (hS : ramseyTriangleBound r ≤ S.card)
    (χ : A → Fin r) :
    ∃ (c : Fin r) (x y z : A),
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
      x + y = z ∧
      χ x = c ∧ χ y = c ∧ χ z = c := by
  rcases addCommGroup_schurs_theorem r hr S hS χ with
    ⟨c, -, -, -, x, y, z, -, -, -, -, -, -, -, -, -, h_sum, hx0, hy0, hz0, hcx, hcy, hcz⟩
  exact ⟨c, x, y, z, hx0, hy0, hz0, h_sum, hcx, hcy, hcz⟩

/-- A subset of an additive group `A` is sum-free if it contains no solution to `x + y = z`. -/
def IsSumFree {A : Type*} [Add A] (s : Finset A) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

/-- **Finite Additive Abelian Group Schur Theorem**:
For any finite additive abelian group $A$ with $|A| \ge \text{ramseyTriangleBound } r$,
every $r$-coloring contains a monochromatic solution to $x + y = z$ with $x, y, z \ne 0$. -/
theorem finite_addCommGroup_schurs_theorem {A : Type*} [Fintype A] [AddCommGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (hA : ramseyTriangleBound r ≤ Fintype.card A)
    (χ : A → Fin r) :
    ∃ (c : Fin r) (x y z : A),
      x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧
      x + y = z ∧
      χ x = c ∧ χ y = c ∧ χ z = c :=
  addCommGroup_schurs_theorem_simple r hr Finset.univ (by rwa [Finset.card_univ]) χ

/-- **Finite Additive Abelian Group Color Classes Not Sum-Free**:
In any $r$-coloring of a finite additive abelian group $A$ with $|A| \ge \text{ramseyTriangleBound } r$,
at least one color class in $A \setminus \{0\}$ is not sum-free. -/
theorem finite_addCommGroup_color_classes_not_sum_free {A : Type*} [Fintype A] [AddCommGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (hA : ramseyTriangleBound r ≤ Fintype.card A)
    (χ : A → Fin r) :
    let A_nonzero := (Finset.univ : Finset A).erase 0
    let colorClass (c : Fin r) : Finset A := A_nonzero.filter (fun x => χ x = c)
    ∃ c : Fin r, ¬ IsSumFree (colorClass c) := by
  intro A_nonzero colorClass
  rcases finite_addCommGroup_schurs_theorem r hr hA χ with ⟨c, x, y, z, hx0, hy0, hz0, hxyz, hcx, hcy, hcz⟩
  have h_in : ∀ {a : A}, a ≠ 0 → χ a = c → a ∈ colorClass c :=
    fun ha hc => Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, hc⟩
  exact ⟨c, fun h_sf => (hxyz ▸ h_sf x (h_in hx0 hcx) y (h_in hy0 hcy)) (h_in hz0 hcz)⟩

/-- **Finite Additive Abelian Group Partition Regularity**:
If $A \setminus \{0\}$ is covered by $r$ sets $A_0, \dots, A_{r-1}$ where $|A| \ge \text{ramseyTriangleBound } r$,
then at least one set $A_i$ contains a non-zero solution to $x + y = z$ ($x, y, z \ne 0$). -/
theorem finite_addCommGroup_partition_regular {A : Type*} [Fintype A] [AddCommGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (hA : ramseyTriangleBound r ≤ Fintype.card A)
    (Sets : Fin r → Finset A)
    (h_cover : (Finset.univ : Finset A).erase 0 ⊆ Finset.biUnion Finset.univ Sets) :
    ∃ i : Fin r, ∃ x y z, x ∈ Sets i ∧ y ∈ Sets i ∧ z ∈ Sets i ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x + y = z := by
  have h_choice : ∀ a : A, ∃ i : Fin r, a ∈ (Finset.univ : Finset A).erase 0 → a ∈ Sets i := by
    intro a
    by_cases ha : a ∈ (Finset.univ : Finset A).erase 0
    · rcases Finset.mem_biUnion.mp (h_cover ha) with ⟨i, -, hi⟩
      exact ⟨i, fun _ => hi⟩
    · exact ⟨⟨0, hr⟩, fun h => (ha h).elim⟩
  let χ : A → Fin r := fun a => (h_choice a).choose
  have hχ : ∀ {a : A}, a ≠ 0 → a ∈ Sets (χ a) :=
    fun ha => (h_choice _).choose_spec (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩)
  rcases finite_addCommGroup_schurs_theorem r hr hA χ with ⟨c, x, y, z, hx0, hy0, hz0, hxyz, hcx, hcy, hcz⟩
  exact ⟨c, x, y, z, hcx ▸ hχ hx0, hcy ▸ hχ hy0, hcz ▸ hχ hz0, hx0, hy0, hz0, hxyz⟩

/-- **Finite Additive Abelian Group Partition Not Sum-Free**:
In any $r$-covering of $A \setminus \{0\}$ with $|A| \ge \text{ramseyTriangleBound } r$,
not all partition classes can be sum-free. -/
theorem finite_addCommGroup_partition_not_sum_free {A : Type*} [Fintype A] [AddCommGroup A] [DecidableEq A]
    (r : ℕ) (hr : 1 ≤ r) (hA : ramseyTriangleBound r ≤ Fintype.card A)
    (Sets : Fin r → Finset A)
    (h_cover : (Finset.univ : Finset A).erase 0 ⊆ Finset.biUnion Finset.univ Sets) :
    ∃ i : Fin r, ¬ IsSumFree (Sets i) := by
  rcases finite_addCommGroup_partition_regular r hr hA Sets h_cover with ⟨i, x, y, z, hx, hy, hz, -, -, -, hxyz⟩
  exact ⟨i, fun h_sf => (hxyz ▸ h_sf x hx y hy) hz⟩

#print axioms group_schurs_theorem
#print axioms group_schurs_theorem_simple
#print axioms finite_group_schurs_theorem
#print axioms finite_group_color_classes_not_product_free
#print axioms finite_group_partition_regular
#print axioms finite_group_partition_not_product_free
#print axioms addGroup_schurs_theorem
#print axioms addCommGroup_schurs_theorem
#print axioms addCommGroup_schurs_theorem_simple
#print axioms finite_addCommGroup_schurs_theorem
#print axioms finite_addCommGroup_color_classes_not_sum_free
#print axioms finite_addCommGroup_partition_regular
#print axioms finite_addCommGroup_partition_not_sum_free

end SchursTheorem
