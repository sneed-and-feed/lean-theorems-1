import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Quasiconvex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Formalization.RadonHelly

/-!
# Lovász's Colorful Helly Theorem (1974 / Bárány 1982) and the Primal-Dual Bridge

This module formalizes **Lovász's Colorful Helly Theorem** (discovered by L. Lovász in 1974;
first published proof by I. Bárány in 1982, Theorem 3.1) and articulates its foundational role
within the **Bárány 1982 Primal-Dual Framework** for combinatorial convexity in $\mathbb{R}^d$.

## The Bárány 1982 Primal-Dual Framework

Imre Bárány's landmark 1982 treatise (*"A generalization of Carathéodory's theorem"*) establishes
a unified triadic architecture bridging point configurations, geometric selection, and convex
intersections across dual perspectives:

```
                  ┌─────────────────────────────────────────────────────────┐
                  │               Bárány 1982 Framework                     │
                  └─────────────────────────────────────────────────────────┘
                                               │
             ┌─────────────────────────────────┼─────────────────────────────────┐
             ▼                                 ▼                                 ▼
   【 Primal Face 】                   【 Selection Link 】                【 Dual Face 】
  Colorful Carathéodory               First Selection Lemma                Colorful Helly
    (Bárány 1982, Thm 1.1)             (Bárány 1982, Thm 2.1)             (Bárány 1982, Thm 3.1)
  Point containment in               Piercing & depth of                 Global intersection of
   colorful simplices                 transversal simplices               colorful convex families
  `Formalization.ColorfulCaratheodory` `Formalization.ColorfulCaratheodory.Selection` `Formalization.ColorfulHelly`
```

### 1. Primal Face (Theorem 1.1: Colorful Carathéodory)
- **Mathematical Statement**: Let $S_0, S_1, \dots, S_d \subset \mathbb{R}^d$ be $d + 1$ sets of points
  such that a target point $p \in \mathbb{R}^d$ belongs to the convex hull of each color class:
  $$\forall i \in \{0, \dots, d\}, \quad p \in \operatorname{conv}(S_i).$$
  Then there exists a **colorful transversal choice** $f \in \prod_{i=0}^d S_i$ (i.e. $f(i) \in S_i$ for each $i$)
  such that $p$ is contained in the resulting colorful simplex:
  $$p \in \operatorname{conv}(\{f(0), f(1), \dots, f(d)\}).$$
- **Sister Module**: Formalized in `Formalization.ColorfulCaratheodory` via
  `ColorfulCaratheodory.colorful_caratheodory_point` and `ColorfulCaratheodory.colorful_caratheodory_origin`.
- **Transversal Predicates**:
  - `ColorfulCaratheodory.IsColorfulChoice S f`: Predicate asserting $f(i) \in S(i)$ for all $i$.
  - `ColorfulCaratheodory.colorfulTransversals S`: The finset of all colorful point selections.
  - `ColorfulCaratheodory.colorfulSimplex f`: The convex hull $\operatorname{conv}(\operatorname{range} f)$.

### 2. Selection Link (Theorem 2.1: First Selection Lemma & Centerpoint)
- **Mathematical Statement**: For any finite point set $P \subset \mathbb{R}^d$, there exists a point $p \in \mathbb{R}^d$
  (a centerpoint / median) contained in a strictly positive fraction $c_d \binom{|P|}{d+1}$ of all $d$-simplices
  spanned by $P$. In the colorful setting, when $p \in \operatorname{conv}(S_i)$ for each color class, colorful
  transversals generate intersecting simplices covering the centerpoint.
- **Sister Module**: Formalized in `Formalization.ColorfulCaratheodory.Selection` via
  `ColorfulCaratheodory.first_selection_lemma_1d`, `ColorfulCaratheodory.colorful_selection_lemma_1d`,
  and `ColorfulCaratheodory.centerpoint_1d`.

### 3. Dual Face (Theorem 3.1: Colorful Helly Theorem)
- **Mathematical Statement (Lovász 1974; Bárány 1982, Theorem 3.1)**:
  Let $\mathcal{F}_0, \mathcal{F}_1, \dots, \mathcal{F}_d$ be $d + 1$ finite families of convex sets in $\mathbb{R}^d$.
  If every **colorful transversal selection** of sets (one set $S_i \in \mathcal{F}_i$ from each color class)
  has a non-empty intersection:
  $$\forall (S_0, \dots, S_d) \in \prod_{i=0}^d \mathcal{F}_i, \quad \bigcap_{i=0}^d S_i \ne \emptyset,$$
  then at least one color family $\mathcal{F}_j$ has a non-empty **global intersection**:
  $$\exists j \in \{0, \dots, d\}, \quad \bigcap_{S \in \mathcal{F}_j} S \ne \emptyset.$$
- **Formalized in this Module**: `ColorfulHelly.colorful_helly`, `ColorfulHelly.colorful_helly_zero`,
  and `ColorfulHelly.colorful_helly_all_dimensions`.
- **Transversal Predicates**:
  - `ColorfulConvexSystem d`: A system of $d+1$ finite families of convex sets.
  - Transversal hypothesis: `∀ choice : (c : Fin (d + 1)) → Set (Fin d → ℝ), (∀ c, choice c ∈ sys.families c) → (⋂ c, choice c).Nonempty`.
  - Invariance under restriction: `ColorfulHelly.transversal_replaceFamily`.

## Geometric Primal-Dual Correspondence

The correspondence between `ColorfulCaratheodory` and `ColorfulHelly` mirrors classical projective and
polar duality in convex geometry:

| Concept / Role | Primal Face (`ColorfulCaratheodory`) | Dual Face (`ColorfulHelly`) |
| :--- | :--- | :--- |
| **Color Classes** | Point sets $S_0, \dots, S_d \subset \mathbb{R}^d$ | Convex families $\mathcal{F}_0, \dots, \mathcal{F}_d \subset \mathcal{P}(\mathbb{R}^d)$ |
| **Colorful Transversal** | Point tuple $(x_0, \dots, x_d) \in \prod S_i$ | Set tuple $(S_0, \dots, S_d) \in \prod \mathcal{F}_i$ |
| **Local Hypothesis** | Origin/point in hull: $p \in \operatorname{conv}(S_i)$ | Non-empty intersection: $\bigcap_{i=0}^d S_i \ne \emptyset$ |
| **Geometric Operation** | Convex hull $\operatorname{conv}(\{x_0, \dots, x_d\})$ | Set intersection $\bigcap_{i=0}^d S_i$ |
| **Global Conclusion** | Existential colorful simplex containing $p$ | Universal point in all sets of *some* color class $\mathcal{F}_j$ |
| **Classical Reduction** | Classical Carathéodory ($|T| \le d+1$) | Classical Helly ($J.card \le d+1 \implies \bigcap F \ne \emptyset$) |

## Architectural Structure & Isolated Classical Benchmark

- `Formalization.RadonHelly`: Serves as the self-contained, isolated classical benchmark suite,
  formalizing Radon's Lemma (Radon 1921) and Helly's Theorem (Helly 1923; Freek Wiedijk #99)
  completely from first principles without external dependencies.
- `Formalization.ColorfulHelly`: Utilizes `RadonHelly.hellys_theorem` during the inductive reduction step
  on compactified extremal witness hulls, demonstrating modular composition between the classical benchmark
  and the colorful combinatorial extension.

## Proof Strategy & Compactification Technique

1. **Finite Witness Extraction**: For each colorful choice of sets, extract a witness point $w \in \bigcap_{c} S_c$.
   Since the number of choices is finite, the pool $W = \operatorname{range}(\text{witness})$ is finite.
2. **Compact Convex Replacement**: Replace each set $S$ with $K(S) = \operatorname{conv}(W \cap S) \subseteq S$.
   $K(S)$ is compact and convex, preserving all colorful transversal intersections.
3. **Extremal Selection**: On each compact intersection $Q(\text{choice}) = \bigcap_c K(\text{choice}(c))$,
   select the unique point $x$ minimizing the squared Euclidean norm $\|x\|^2$, and maximize this minimum over all choices.
4. **Helly Dimension Reduction**: Adjoining the open sublevel set $\{x \mid \|x\|^2 < \|x^*\|^2\}$ to the family and
   applying Helly's theorem (`RadonHelly.hellys_theorem`) shows that at most $d$ sets determine the minimum, leaving
   at least one omitted color index $k$.
5. **Strict Convexity & Global Intersection**: Replacing the set at color $k$ with any other $S \in \mathcal{F}_k$
   and using the strict convexity of the Euclidean norm forces $x^*$ to lie in every set of family $\mathcal{F}_k$.

## References
* I. Bárány, *A generalization of Carathéodory's theorem*, Discrete Mathematics 40 (1982),
  141–152, Theorem 3.1, p. 144; proof pp. 150–151.
  https://doi.org/10.1016/0012-365X(82)90115-7
* L. Lovász, *Problem 206*, Matematikai Lapok 25 (1974), p. 181.
* E. Helly, *Über Mengen konvexer Körper mit gemeinschaftlichen Punkten*, Jahresber. Deutsch. Math.-Verein. 32 (1923), 175–176.
-/

open BigOperators

/-- A Colorful Convex System in $\mathbb{R}^d$ consisting of $d + 1$ finite families of convex sets.
This is the dual counterpart to a system of $d + 1$ point sets in `Formalization.ColorfulCaratheodory`. -/
structure ColorfulConvexSystem (d : ℕ) where
  /-- The $d + 1$ color classes of finite families of sets in $\mathbb{R}^d$. -/
  families : Fin (d + 1) → Finset (Set (Fin d → ℝ))
  /-- Every set belonging to any color family is convex. -/
  h_convex : ∀ (c : Fin (d + 1)) (S : Set (Fin d → ℝ)), S ∈ families c → Convex ℝ S

namespace ColorfulHelly

-- ============================================================================
-- Section 1: Helper Lemmas & Convex Geometry Utilities
-- ============================================================================

/-- Characterization of membership in the intersection of a finset of sets. -/
lemma mem_iInter_finset {α : Type*} (F : Finset (Set α)) (x : α) :
    x ∈ (⋂ S ∈ F, S) ↔ ∀ S ∈ F, x ∈ S := by
  simp only [Set.mem_iInter]

/-- The square of the Euclidean length, written in coordinates: $\sum_i (x_i)^2$.
We use this coordinate-based formulation rather than the ambient sup-norm on `Fin d → ℝ`
because its strict convexity enables unique projection and extremal point arguments.
This matches `ColorfulCaratheodory.euclideanSq` in `Formalization.ColorfulCaratheodory.Basic`. -/
private def euclideanSq (d : ℕ) (x : Fin d → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- The squared Euclidean norm is continuous on `Fin d → ℝ`. -/
private lemma continuous_euclideanSq (d : ℕ) : Continuous (euclideanSq d) :=
  continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2

/-- The squared Euclidean norm is convex on all of $\mathbb{R}^d$. -/
private lemma convexOn_euclideanSq (d : ℕ) : ConvexOn ℝ Set.univ (euclideanSq d) :=
  ⟨convex_univ, fun x _ y _ a b ha hb _ ↦ by
    dsimp [euclideanSq]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ ↦ by
      have := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x i - y i)); nlinarith⟩

/-- Strict sublevel sets $\{x \mid \|x\|^2 < r\}$ of the squared Euclidean norm are convex. -/
private lemma convex_euclideanSq_lt (d : ℕ) (r : ℝ) :
    Convex ℝ {x : Fin d → ℝ | euclideanSq d x < r} := by
  simpa only [Set.mem_univ, true_and] using (convexOn_euclideanSq d).convex_lt r

/-- The squared Euclidean norm is non-negative everywhere. -/
private lemma euclideanSq_nonneg (d : ℕ) (x : Fin d → ℝ) : 0 ≤ euclideanSq d x :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- The squared Euclidean norm vanishes if and only if $x = 0$. -/
private lemma euclideanSq_eq_zero_iff (d : ℕ) (x : Fin d → ℝ) :
    euclideanSq d x = 0 ↔ x = 0 := by
  simp only [euclideanSq, Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _,
    Finset.mem_univ, forall_true_left, sq_eq_zero_iff, funext_iff, Pi.zero_apply]

/-- Strict convexity property of the squared Euclidean norm:
for two distinct points $x \ne y$ with equal squared norm, their midpoint has
strictly smaller squared norm. -/
private lemma euclideanSq_midpoint_lt {d : ℕ} {x y : Fin d → ℝ}
    (hxy : x ≠ y) (heq : euclideanSq d x = euclideanSq d y) :
    euclideanSq d ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • y) < euclideanSq d x := by
  have hdiff : 0 < euclideanSq d (x - y) :=
    (euclideanSq_nonneg d (x - y)).lt_of_ne' fun h ↦
      hxy (sub_eq_zero.mp ((euclideanSq_eq_zero_iff d (x - y)).mp h))
  have hid : (∑ i, ((2 : ℝ)⁻¹ * x i + (2 : ℝ)⁻¹ * y i) ^ 2) =
      ((∑ i, (x i) ^ 2) + (∑ i, (y i) ^ 2)) / 2 - (∑ i, (x i - y i) ^ 2) / 4 := by
    rw [Finset.sum_congr rfl (fun i _ ↦ show ((2 : ℝ)⁻¹ * x i + (2 : ℝ)⁻¹ * y i) ^ 2 =
      ((x i) ^ 2 + (y i) ^ 2) / 2 - (x i - y i) ^ 2 / 4 by ring), Finset.sum_sub_distrib]
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib]
  change (∑ i, ((2 : ℝ)⁻¹ * x i + (2 : ℝ)⁻¹ * y i) ^ 2) < ∑ i, (x i) ^ 2
  change 0 < ∑ i, (x i - y i) ^ 2 at hdiff
  change (∑ i, (x i) ^ 2) = ∑ i, (y i) ^ 2 at heq
  linarith [hid]

/-- If any color family is empty, Colorful Helly holds vacuously because the empty
intersection is the whole universe. -/
lemma colorful_helly_of_empty (d : ℕ) (sys : ColorfulConvexSystem d)
    (h_empty : ∃ (c : Fin (d + 1)), sys.families c = ∅) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty :=
  let ⟨c, hc⟩ := h_empty; ⟨c, 0, by simp [hc]⟩

/-- Helly's Theorem specialized to finsets of convex sets in $\mathbb{R}^d$, derived from the
classical benchmark `RadonHelly.hellys_theorem`. -/
lemma finset_helly (d : ℕ) (F : Finset (Set (Fin d → ℝ)))
    (h_convex : ∀ S ∈ F, Convex ℝ S)
    (h_sub : ∀ G : Finset (Set (Fin d → ℝ)), G ⊆ F → G.card ≤ d + 1 → (⋂ S ∈ G, S).Nonempty) :
    (⋂ S ∈ F, S).Nonempty := by
  have h_inter (J : Finset F) (hJ : J.card ≤ d + 1) : (⋂ i ∈ J, (i.1 : Set (Fin d → ℝ))).Nonempty := by
    obtain ⟨x, hx⟩ := h_sub (J.image Subtype.val) (fun _ hS ↦ by
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hS; exact x.2)
      ((Finset.card_image_le (s := J) (f := Subtype.val)).trans hJ)
    exact ⟨x, by simp only [Set.mem_iInter] at hx ⊢; exact fun i hi ↦ hx i.1 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
  obtain ⟨x, hx⟩ := RadonHelly.hellys_theorem (fun (i : F) ↦ i.1) (fun i ↦ h_convex i.1 i.2) h_inter
  exact ⟨x, by simp only [Set.mem_iInter] at hx ⊢; exact fun S hS ↦ hx ⟨S, hS⟩⟩

/-- If a family has cardinality 1, its global intersection is non-empty under the colorful
transversal hypothesis. -/
lemma family_nonempty_of_card_one (d : ℕ) (sys : ColorfulConvexSystem d)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty)
    (h_nonempty : ∀ c, (sys.families c).Nonempty)
    (c0 : Fin (d + 1)) (hc0 : (sys.families c0).card = 1) :
    (⋂ S ∈ sys.families c0, S).Nonempty := by
  obtain ⟨S0, hS0⟩ := Finset.card_eq_one.mp hc0
  choose ch hch using h_nonempty
  obtain ⟨x, hx⟩ := h_transversal (fun c ↦ if c = c0 then S0 else ch c) fun c ↦ by
    split_ifs with hc
    · subst hc; rw [hS0]; exact Finset.mem_singleton_self S0
    · exact hch c
  refine ⟨x, by simp only [Set.mem_iInter, hS0, Finset.mem_singleton]; rintro S rfl; simpa using Set.mem_iInter.mp hx c0⟩

-- ============================================================================
-- Section 2: Family Replacement Operations & Transversal Invariance
-- ============================================================================

/-- Replace family $k$ in `sys` with a subcollection $G \subseteq \text{sys.families}(k)$. -/
def replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k) : ColorfulConvexSystem d where
  families c := if c = k then G else sys.families c
  h_convex c S hS := by
    split_ifs at hS with hc
    · subst c; exact sys.h_convex k S (hG S hS)
    · exact sys.h_convex c S hS

/-- Total size of the system after replacing family $k$ with $G$. -/
lemma card_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k) :
    ∑ c, ((replaceFamily d sys k G hG).families c).card =
      (∑ c ∈ Finset.univ.erase k, (sys.families c).card) + G.card := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun c hc ↦ ?_
    dsimp [replaceFamily]
    simp [Finset.mem_erase.mp hc |>.1]
  · dsimp [replaceFamily]; simp

/-- **Transversal Invariance under Subcollection Replacement**:
If every colorful transversal in `sys` has non-empty intersection, then replacing any family $k$
with a subcollection $G \subseteq \text{sys.families}(k)$ preserves the transversal intersection property.
This is the dual analog to restriction of colorful choices in `Formalization.ColorfulCaratheodory.Transversals`. -/
lemma transversal_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) → (⋂ c, choice c).Nonempty) :
    ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ (replaceFamily d sys k G hG).families c) →
      (⋂ c, choice c).Nonempty := fun choice h_choice ↦
  h_transversal choice fun c ↦ by
    have hc := h_choice c
    dsimp [replaceFamily] at hc
    split_ifs at hc with hck
    · subst c; exact hG (choice k) hc
    · exact hc

/-- If a winning color family $w \ne k$ has non-empty intersection in the reduced system,
then it already has non-empty global intersection in the original system. -/
lemma winner_of_replaceFamily (d : ℕ) (sys : ColorfulConvexSystem d) (k : Fin (d + 1))
    (G : Finset (Set (Fin d → ℝ))) (hG : ∀ S ∈ G, S ∈ sys.families k)
    (w : Fin (d + 1))
    (hw : (⋂ S ∈ (replaceFamily d sys k G hG).families w, S).Nonempty)
    (hw_ne : w ≠ k) :
    (⋂ S ∈ sys.families w, S).Nonempty := by
  have : (replaceFamily d sys k G hG).families w = sys.families w := by
    dsimp [replaceFamily]; simp [hw_ne]
  rwa [this] at hw

-- ============================================================================
-- Section 3: Inductive Framework & Extremal Witness Reduction
-- ============================================================================

/-- **Inductive Core of Lovász's Colorful Helly Theorem (Bárány 1982, Theorem 3.1)**:
For dimension $d \ge 1$, if every colorful transversal of $d+1$ convex families intersects,
then at least one family has a non-empty global intersection.

### Proof Architecture:
1. **Transversal Witness Pool**: Extract a finite pool of witnesses $W \subset \mathbb{R}^d$
   from the finitely many colorful transversals.
2. **Compactification**: Replace each convex set $S$ by the compact convex hull $K(S) = \operatorname{conv}(W \cap S) \subseteq S$.
3. **Extremal Selection**: Find the choice maximizing the minimum squared Euclidean norm of $Q(\text{choice}) = \bigcap_c K(\text{choice}(c))$.
4. **Sublevel Set Separation via Classical Helly**: Apply Helly's theorem (`RadonHelly.hellys_theorem`) to the adjoined strict sublevel set
   $\{x \mid \|x\|^2 < \|x^*\|^2\}$. A subset $J$ of size $\le d + 1$ with empty intersection must contain the sublevel set,
   leaving an unused color index $k \notin J$.
5. **Strict Convexity Perturbation**: Replacing the set at color $k$ with any $S \in \mathcal{F}_k$ and invoking the strict convexity
   of `euclideanSq` forces $x^* \in K(S) \subseteq S$, establishing $x^* \in \bigcap_{S \in \mathcal{F}_k} S$. -/
lemma colorful_helly_inductive (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (sys : ColorfulConvexSystem d)
    (_h_size : ∑ c, (sys.families c).card = n)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty := by
  classical
  by_cases h_empty : ∃ c, sys.families c = ∅
  · exact colorful_helly_of_empty d sys h_empty
  have h_nonempty c : (sys.families c).Nonempty := Finset.nonempty_iff_ne_empty.2 fun hc ↦ h_empty ⟨c, hc⟩

  let Choice := (c : Fin (d + 1)) → sys.families c
  have hChoice : Nonempty Choice :=
    let ⟨S, hS⟩ := Classical.axiomOfChoice h_nonempty; ⟨fun c ↦ ⟨S c, hS c⟩⟩
  have hChoice_univ : (Finset.univ : Finset Choice).Nonempty := ⟨Classical.choice hChoice, Finset.mem_univ _⟩

  let witness (choice : Choice) : Fin d → ℝ :=
    Classical.choose (h_transversal (fun c ↦ (choice c : Set (Fin d → ℝ))) fun c ↦ (choice c).property)
  have witness_mem (choice : Choice) (c : Fin (d + 1)) : witness choice ∈ (choice c : Set (Fin d → ℝ)) :=
    Set.mem_iInter.mp (Classical.choose_spec (h_transversal _ fun c ↦ (choice c).2)) c

  let W : Set (Fin d → ℝ) := Set.range witness
  let K (S : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := convexHull ℝ (W ∩ S)
  have hK_compact (S : Set (Fin d → ℝ)) : IsCompact (K S) :=
    (Set.finite_range witness |>.inter_of_left S).isCompact_convexHull ℝ
  have hK_convex (S : Set (Fin d → ℝ)) : Convex ℝ (K S) := convex_convexHull ℝ (W ∩ S)
  have hK_subset (c : Fin (d + 1)) (S : sys.families c) : K (S : Set (Fin d → ℝ)) ⊆ (S : Set (Fin d → ℝ)) :=
    convexHull_min Set.inter_subset_right (sys.h_convex c S S.2)
  have witness_mem_K (choice : Choice) (c : Fin (d + 1)) : witness choice ∈ K (choice c : Set (Fin d → ℝ)) :=
    subset_convexHull ℝ (W ∩ (choice c : Set (Fin d → ℝ))) ⟨⟨choice, rfl⟩, witness_mem choice c⟩

  let Q (choice : Choice) : Set (Fin d → ℝ) := ⋂ c, K (choice c : Set (Fin d → ℝ))
  have hQ_compact (choice : Choice) : IsCompact (Q choice) :=
    (hK_compact (choice ⟨0, Nat.succ_pos d⟩)).of_isClosed_subset
      (isClosed_iInter fun c ↦ (hK_compact (choice c)).isClosed) (Set.iInter_subset _ _)
  have h_min (choice : Choice) : ∃ x ∈ Q choice, IsMinOn (euclideanSq d) (Q choice) x :=
    (hQ_compact choice).exists_isMinOn ⟨witness choice, Set.mem_iInter_of_mem (witness_mem_K choice)⟩
      (continuous_euclideanSq d).continuousOn
  let closest (choice : Choice) : Fin d → ℝ := Classical.choose (h_min choice)
  have closest_mem (choice : Choice) : closest choice ∈ Q choice := (Classical.choose_spec (h_min choice)).1
  have closest_min (choice : Choice) {x : Fin d → ℝ} (hx : x ∈ Q choice) :
      euclideanSq d (closest choice) ≤ euclideanSq d x := (Classical.choose_spec (h_min choice)).2 hx

  obtain ⟨best, -, hbest⟩ := Finset.exists_max_image Finset.univ (fun c ↦ euclideanSq d (closest c)) hChoice_univ
  let extSet : Option (Fin (d + 1)) → Set (Fin d → ℝ)
    | none => {x | euclideanSq d x < euclideanSq d (closest best)}
    | some c => K (best c : Set (Fin d → ℝ))
  have h_ext_convex : ∀ i, Convex ℝ (extSet i)
    | none => convex_euclideanSq_lt d _
    | some c => hK_convex (best c)
  have h_ext_empty : ¬(⋂ i, extSet i).Nonempty := fun ⟨x, hx⟩ ↦
    not_lt_of_ge (closest_min best (Set.mem_iInter.2 fun c ↦ Set.mem_iInter.mp hx (some c)))
      (Set.mem_iInter.mp hx none)
  have ⟨J, hJ_card, hJ_empty⟩ : ∃ J : Finset (Option (Fin (d + 1))), J.card ≤ d + 1 ∧ ¬(⋂ i ∈ J, extSet i).Nonempty := by
    by_contra h
    exact h_ext_empty (RadonHelly.hellys_theorem extSet h_ext_convex fun J hJ ↦
      by_contra fun hne ↦ h ⟨J, hJ, hne⟩)
  have hnone : none ∈ J := by
    by_contra hnone; apply hJ_empty; refine ⟨closest best, ?_⟩
    simp only [Set.mem_iInter]; rintro (_ | c) hi
    · exact (hnone hi).elim
    · exact Set.mem_iInter.mp (closest_mem best) c

  let colored : Finset (Option (Fin (d + 1))) := Finset.image some Finset.univ
  have h_erase_card : (J.erase none).card < colored.card := by
    rw [Finset.card_erase_of_mem hnone, show colored.card = d + 1 by
      dsimp [colored]
      rw [Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_univ, Fintype.card_fin]]
    omega
  obtain ⟨i, hi_colored, hi_erase⟩ := Finset.exists_mem_notMem_of_card_lt_card h_erase_card
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi_colored
  have hkJ : some k ∉ J := fun hk ↦ hi_erase (Finset.mem_erase.mpr ⟨Option.some_ne_none k, hk⟩)

  have determinant_lower {x : Fin d → ℝ} (hx : ∀ c, some c ∈ J → x ∈ K (best c : Set (Fin d → ℝ))) :
      euclideanSq d (closest best) ≤ euclideanSq d x := by
    by_contra hle; apply hJ_empty; refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]; rintro (_ | c) hi
    · exact lt_of_not_ge hle
    · exact hx c hi

  refine ⟨k, closest best, by
    simp only [Set.mem_iInter]
    intro S hS
    let Sk : sys.families k := ⟨S, hS⟩
    let replacement : Choice := fun c ↦ if hc : c = k then hc ▸ Sk else best c
    have replacement_eq (c : Fin (d + 1)) (hc : c ≠ k) : replacement c = best c := by simp [replacement, hc]
    have hrep_ge : euclideanSq d (closest best) ≤ euclideanSq d (closest replacement) :=
      determinant_lower fun c hcJ ↦ by
        have hck : c ≠ k := fun h ↦ hkJ (h ▸ hcJ)
        rw [← replacement_eq c hck]
        exact Set.mem_iInter.mp (closest_mem replacement) c
    have hrep_value : euclideanSq d (closest replacement) = euclideanSq d (closest best) :=
      le_antisymm (hbest replacement (Finset.mem_univ _)) hrep_ge
    have hrep_point : closest replacement = closest best := by
      by_contra hne
      let midpoint := (2 : ℝ)⁻¹ • closest replacement + (2 : ℝ)⁻¹ • closest best
      have hmid_constraints (c : Fin (d + 1)) (hcJ : some c ∈ J) : midpoint ∈ K (best c : Set (Fin d → ℝ)) := by
        have hck : c ≠ k := fun h ↦ hkJ (h ▸ hcJ)
        exact hK_convex (best c) (by rw [← replacement_eq c hck]; exact Set.mem_iInter.mp (closest_mem replacement) c)
          (Set.mem_iInter.mp (closest_mem best) c) (by norm_num) (by norm_num) (by norm_num)
      have hmid_ge := determinant_lower hmid_constraints
      have hmid_lt : euclideanSq d midpoint < euclideanSq d (closest replacement) :=
        euclideanSq_midpoint_lt hne hrep_value
      linarith
    have hrep_K : closest replacement ∈ K S := by
      have := Set.mem_iInter.mp (closest_mem replacement) k
      simpa [replacement, Sk] using this
    rw [hrep_point] at hrep_K
    exact hK_subset k Sk hrep_K⟩

-- ============================================================================
-- Section 4: Main Theorems (Lovász 1974; first published proof, Bárány 1982)
-- ============================================================================

/-- **Lovász's Colorful Helly Theorem in Dimension 0**:
In dimension $d = 0$, there is a single color class $c = 0$, and the ambient space `Fin 0 → ℝ`
consists of a unique point $0$. The transversal hypothesis guarantees that any selection $S \in \mathcal{F}_0$
contains this point, so $0 \in \bigcap_{S \in \mathcal{F}_0} S \ne \emptyset$. -/
lemma colorful_helly_zero (sys : ColorfulConvexSystem 0)
    (h_transversal : ∀ (choice : (c : Fin 1) → Set (Fin 0 → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin 1, choice c).Nonempty) :
    ∃ (j : Fin 1), (⋂ S ∈ sys.families j, S).Nonempty := by
  refine ⟨0, 0, ?_⟩
  simp only [Set.mem_iInter]
  intro S hS
  have hchoice_mem (c : Fin 1) : S ∈ sys.families c := by simpa only [Subsingleton.elim c 0] using hS
  obtain ⟨x, hx⟩ := h_transversal (fun _ ↦ S) hchoice_mem
  have hxS : x ∈ S := Set.mem_iInter.mp hx 0
  simpa only [Subsingleton.elim x 0] using hxS

/-- **Lovász's Colorful Helly Theorem (General Dimension $d \ge 1$, Bárány 1982, Theorem 3.1)**:
Let $\mathcal{F}_0, \dots, \mathcal{F}_d$ be $d+1$ finite families of convex sets in $\mathbb{R}^d$.
If every colorful transversal selection $S_i \in \mathcal{F}_i$ ($i \in \{0, \dots, d\}$) has a non-empty
intersection $\bigcap_{i=0}^d S_i \ne \emptyset$, then at least one family $\mathcal{F}_j$ has a non-empty
global intersection:
$$\exists j \in \{0, \dots, d\}, \quad \bigcap_{S \in \mathcal{F}_j} S \ne \emptyset.$$

### Dual Bridge:
This theorem constitutes the **Dual Face** of the **Bárány 1982 Primal-Dual Framework**, serving
as the exact geometric dual to Bárány's Colorful Carathéodory Theorem
(`ColorfulCaratheodory.colorful_caratheodory_point` in `Formalization.ColorfulCaratheodory`). -/
theorem colorful_helly (d : ℕ) (hd : 1 ≤ d) (sys : ColorfulConvexSystem d)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty :=
  colorful_helly_inductive d hd (∑ c, (sys.families c).card) sys rfl h_transversal

/-- **Lovász's Colorful Helly Theorem in All Dimensions $d \in \mathbb{N}$**:
Unified statement encompassing both $d = 0$ (`colorful_helly_zero`) and $d \ge 1$ (`colorful_helly`).
If all colorful selections of $d + 1$ convex sets intersect, at least one color family has a
non-empty global intersection. -/
theorem colorful_helly_all_dimensions (d : ℕ) (sys : ColorfulConvexSystem d)
    (h_transversal : ∀ (choice : (c : Fin (d + 1)) → Set (Fin d → ℝ)),
      (∀ c, choice c ∈ sys.families c) →
      (⋂ c : Fin (d + 1), choice c).Nonempty) :
    ∃ (j : Fin (d + 1)), (⋂ S ∈ sys.families j, S).Nonempty := by
  cases d with
  | zero => exact colorful_helly_zero sys h_transversal
  | succ d => exact colorful_helly (d + 1) (Nat.succ_le_succ (Nat.zero_le d)) sys h_transversal

end ColorfulHelly

#print axioms ColorfulHelly.colorful_helly_inductive
#print axioms ColorfulHelly.colorful_helly_zero
#print axioms ColorfulHelly.colorful_helly
#print axioms ColorfulHelly.colorful_helly_all_dimensions
