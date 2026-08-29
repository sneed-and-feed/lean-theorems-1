import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

open BigOperators Finset
open Classical

noncomputable section

namespace ColorfulCaratheodory

variable {d : ℕ}

/-- Predicate stating that `f` is a colorful choice (transversal) from a family of sets `S`. -/
def IsColorfulChoice {d : ℕ} (S : Fin (d + 1) → Set (Fin d → ℝ)) (f : Fin (d + 1) → Fin d → ℝ) : Prop :=
  ∀ i : Fin (d + 1), f i ∈ S i

/-- The colorful simplex (convex hull of the points) formed by a transversal `f`. -/
def colorfulSimplex {d : ℕ} (f : Fin (d + 1) → Fin d → ℝ) : Set (Fin d → ℝ) :=
  convexHull ℝ (Set.range f)

/-- Colorful choice predicate specialized to finsets. -/
def IsColorfulChoiceFinset (S : Fin (d + 1) → Finset (Fin d → ℝ)) (f : Fin (d + 1) → Fin d → ℝ) : Prop :=
  ∀ i : Fin (d + 1), f i ∈ S i

/-- **Classical Carathéodory Theorem as a Deduction from Colorful Selection**:
Deduction of the classical Carathéodory bound $|T| \le d + 1$ from Bárány's colorful transversal selection. -/
theorem caratheodory_classical_deduction (S_single : Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (hp : p ∈ convexHull ℝ S_single)
    (h_colorful : ∃ f : Fin (d + 1) → Fin d → ℝ,
      IsColorfulChoice (fun _ ↦ S_single) f ∧ p ∈ colorfulSimplex f) :
    ∃ (T : Finset (Fin d → ℝ)), (T : Set (Fin d → ℝ)) ⊆ S_single ∧ T.card ≤ d + 1 ∧ p ∈ convexHull ℝ (T : Set (Fin d → ℝ)) := sorry

/-- **Colorful Carathéodory Theorem in Dimension 1**:
For any two color classes $S_0, S_1 \subset \mathbb{R}^1$ whose convex hulls both contain $p$,
there exists a colorful transversal $f$ ($f(0) \in S_0, f(1) \in S_1$) such that $p \in \operatorname{conv}(\operatorname{range} f)$. -/
theorem colorful_caratheodory_dim1 (S : Fin 2 → Set (Fin 1 → ℝ)) (p : Fin 1 → ℝ)
    (hp : ∀ i : Fin 2, p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 2 → Fin 1 → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := sorry

/-- **Colorful Carathéodory Theorem in Dimension 2 (Colorful Triangle Theorem)**:
For any three color classes $S_0, S_1, S_2 \subset \mathbb{R}^2$ whose convex hulls all contain $p$,
there exists a colorful transversal $f$ ($f(0) \in S_0, f(1) \in S_1, f(2) \in S_2$)
such that $p \in \operatorname{conv}(\operatorname{range} f)$. -/
theorem colorful_caratheodory_dim2 (S : Fin 3 → Set (Fin 2 → ℝ)) (p : Fin 2 → ℝ)
    (hp : ∀ i : Fin 3, p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin 3 → Fin 2 → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := sorry

/-- **Bárány's Colorful Carathéodory Theorem (General Point Form, 1982)**:
Let $S_0, \dots, S_d \subset \mathbb{R}^d$ be $d+1$ sets of points such that a target point
$p \in \mathbb{R}^d$ belongs to the convex hull of each set:
$$p \in \operatorname{conv}(S_i) \quad \text{for all } i \in \{0, 1, \dots, d\}.$$
Then there exists a colorful choice $f$ ($f(i) \in S_i$ for each $i$) such that $p$ lies
in the colorful simplex formed by $f$:
$$p \in \operatorname{conv}(\operatorname{range} f) = \operatorname{conv}(\{f(0), \dots, f(d)\}).$$ -/
theorem colorful_caratheodory_point (S : Fin (d + 1) → Set (Fin d → ℝ)) (p : Fin d → ℝ)
    (hp : ∀ i : Fin (d + 1), p ∈ convexHull ℝ (S i)) :
    ∃ f : Fin (d + 1) → Fin d → ℝ, IsColorfulChoice S f ∧ p ∈ colorfulSimplex f := sorry

/-- **Bárány's Colorful Carathéodory Theorem (Origin Form, 1982)**:
If the origin $0 \in \mathbb{R}^d$ belongs to the convex hull of each of the $d + 1$
color classes $S_i \subset \mathbb{R}^d$, then there exists a colorful choice $f$
such that $0 \in \operatorname{conv}(\operatorname{range} f)$. -/
theorem colorful_caratheodory_origin (S : Fin (d + 1) → Set (Fin d → ℝ))
    (h_origin : ∀ i : Fin (d + 1), (0 : Fin d → ℝ) ∈ convexHull ℝ (S i)) :
    ∃ f : Fin (d + 1) → Fin d → ℝ, IsColorfulChoice S f ∧ (0 : Fin d → ℝ) ∈ colorfulSimplex f := sorry

/-- **Centerpoint Theorem in Dimension 1**:
For any finite nonempty set $P \subset \mathbb{R}^1$, there exists a centerpoint $p \in \mathbb{R}^1$
(the median) such that every closed half-line containing $p$ contains at least $(|P| + 1) / 2$ points of $P$. -/
theorem centerpoint_1d (P : Finset (Fin 1 → ℝ)) (hP : P.Nonempty) :
    ∃ p : Fin 1 → ℝ,
      (P.card + 1) / 2 ≤ (P.filter (fun x ↦ x 0 ≤ p 0)).card ∧
      (P.card + 1) / 2 ≤ (P.filter (fun x ↦ p 0 ≤ x 0)).card := sorry

/-- **Bárány's First Selection Lemma in Dimension 1**:
For any finite set $P \subset \mathbb{R}^1$ with $|P| \ge 2$, there exists a point $p \in \mathbb{R}^1$
contained in at least $(|P| / 2) \cdot (|P| - |P| / 2)$ pairs $\{a, b\} \subseteq P$ whose convex hull contains $p$. -/
theorem first_selection_lemma_1d (P : Finset (Fin 1 → ℝ)) (hP : 2 ≤ P.card) :
    ∃ p : Fin 1 → ℝ,
      (P.card / 2) * (P.card - P.card / 2) ≤
        ((P.powersetCard 2).filter (fun (s : Finset (Fin 1 → ℝ)) ↦ p ∈ convexHull ℝ (s : Set (Fin 1 → ℝ)))).card := sorry

/-- **Colorful Selection Lemma in Dimension 1**:
For any two finite color classes $S_0, S_1 \subset \mathbb{R}^1$ whose convex hulls both contain a point $p$,
there exists at least one colorful pair $(a, b) \in S_0 \times S_1$ whose convex hull contains $p$. -/
theorem colorful_selection_lemma_1d (S : Fin 2 → Finset (Fin 1 → ℝ)) (p : Fin 1 → ℝ)
    (hp : ∀ i : Fin 2, p ∈ convexHull ℝ (S i : Set (Fin 1 → ℝ))) :
    1 ≤ ((S 0 ×ˢ S 1).filter (fun (ab : (Fin 1 → ℝ) × (Fin 1 → ℝ)) ↦
      p ∈ convexHull ℝ ({ab.1, ab.2} : Set (Fin 1 → ℝ)))).card := sorry

end ColorfulCaratheodory
