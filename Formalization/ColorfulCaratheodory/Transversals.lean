import Formalization.ColorfulCaratheodory.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Choose

open BigOperators Finset

noncomputable section

namespace ColorfulCaratheodory

variable {d : ℕ}

/-- Colorful transversal type: dependent functions selecting an element from each color class. -/
def ColorfulChoice (S : Fin (d + 1) → Finset (Fin d → ℝ)) :=
  (i : Fin (d + 1)) → { x : Fin d → ℝ // x ∈ S i }

instance (S : Fin (d + 1) → Finset (Fin d → ℝ)) : Fintype (ColorfulChoice S) := by
  dsimp [ColorfulChoice]; infer_instance

/-- The point selection function associated to a colorful choice. -/
def ColorfulChoice.val {S : Fin (d + 1) → Finset (Fin d → ℝ)} (c : ColorfulChoice S) :
    Fin (d + 1) → (Fin d → ℝ) := fun i ↦ (c i).1

lemma ColorfulChoice.val_mem {S : Fin (d + 1) → Finset (Fin d → ℝ)} (c : ColorfulChoice S) (i : Fin (d + 1)) :
    c.val i ∈ S i := (c i).2

/-- Finset of all colorful point selections. -/
def colorfulTransversals (S : Fin (d + 1) → Finset (Fin d → ℝ)) :
    Finset (Fin (d + 1) → (Fin d → ℝ)) :=
  (Finset.univ : Finset (ColorfulChoice S)).image ColorfulChoice.val

lemma mem_colorfulTransversals_iff (S : Fin (d + 1) → Finset (Fin d → ℝ))
    (f : Fin (d + 1) → (Fin d → ℝ)) :
    f ∈ colorfulTransversals S ↔ ∀ i : Fin (d + 1), f i ∈ S i := by
  simp only [colorfulTransversals, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨c, hc⟩ i ↦ hc ▸ (c i).2, fun hf ↦ ⟨fun i ↦ ⟨f i, hf i⟩, rfl⟩⟩

lemma colorfulTransversals_nonempty_iff (S : Fin (d + 1) → Finset (Fin d → ℝ)) :
    (colorfulTransversals S).Nonempty ↔ ∀ i : Fin (d + 1), (S i).Nonempty := by
  simp_rw [Finset.Nonempty, mem_colorfulTransversals_iff]
  exact ⟨fun ⟨f, hf⟩ i ↦ ⟨f i, hf i⟩, fun h ↦ by choose f hf using h; exact ⟨f, hf⟩⟩

lemma colorfulChoice_nonempty_iff (S : Fin (d + 1) → Finset (Fin d → ℝ)) :
    Nonempty (ColorfulChoice S) ↔ ∀ i : Fin (d + 1), (S i).Nonempty := by
  simp_rw [Finset.Nonempty]
  exact ⟨fun ⟨c⟩ i ↦ ⟨(c i).1, (c i).2⟩, fun h ↦ by choose f hf using h; exact ⟨fun i ↦ ⟨f i, hf i⟩⟩⟩

/-- Update a colorful choice at coordinate `k` with a new point `s ∈ S k`. -/
def updateColorfulChoice {S : Fin (d + 1) → Finset (Fin d → ℝ)} (c : ColorfulChoice S)
    (k : Fin (d + 1)) (s : Fin d → ℝ) (hs : s ∈ S k) : ColorfulChoice S :=
  fun i ↦ if h : i = k then ⟨s, by subst h; exact hs⟩ else c i

@[simp]
lemma updateColorfulChoice_same {S : Fin (d + 1) → Finset (Fin d → ℝ)} (c : ColorfulChoice S)
    (k : Fin (d + 1)) (s : Fin d → ℝ) (hs : s ∈ S k) :
    (updateColorfulChoice c k s hs).val k = s := by
  dsimp [updateColorfulChoice, ColorfulChoice.val]; simp

@[simp]
lemma updateColorfulChoice_ne {S : Fin (d + 1) → Finset (Fin d → ℝ)} (c : ColorfulChoice S)
    (k : Fin (d + 1)) (s : Fin d → ℝ) (hs : s ∈ S k)
    {i : Fin (d + 1)} (hik : i ≠ k) :
    (updateColorfulChoice c k s hs).val i = c.val i := by
  dsimp [updateColorfulChoice, ColorfulChoice.val]; simp [hik]

lemma range_updateColorfulChoice {S : Fin (d + 1) → Finset (Fin d → ℝ)} (c : ColorfulChoice S)
    (k : Fin (d + 1)) (s : Fin d → ℝ) (hs : s ∈ S k) :
    Set.range (updateColorfulChoice c k s hs).val = insert s (c.val '' (Set.univ \ {k})) := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_image, Set.mem_sdiff, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hik : i = k
    · subst hik; exact Or.inl (updateColorfulChoice_same c i s hs)
    · exact Or.inr ⟨i, hik, (updateColorfulChoice_ne c k s hs hik).symm⟩
  · rintro (rfl | ⟨i, hik, rfl⟩)
    · exact ⟨k, updateColorfulChoice_same c k _ hs⟩
    · exact ⟨i, updateColorfulChoice_ne c k s hs hik⟩

end ColorfulCaratheodory
