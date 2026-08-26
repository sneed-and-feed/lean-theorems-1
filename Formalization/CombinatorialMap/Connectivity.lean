import Formalization.CombinatorialMap.Basic

variable {D : Type*} [Fintype D] [DecidableEq D]

inductive CombinatorialMap.Reachable (M : CombinatorialMap D) : D → D → Prop where
  | refl : ∀ d, Reachable M d d
  | sigma : ∀ {d₁ d₂}, Reachable M d₁ d₂ → Reachable M d₁ (M.σ d₂)
  | alpha : ∀ {d₁ d₂}, Reachable M d₁ d₂ → Reachable M d₁ (M.α d₂)
  | sigma_inv : ∀ {d₁ d₂}, Reachable M d₁ d₂ → Reachable M d₁ (M.σ⁻¹ d₂)
  | alpha_inv : ∀ {d₁ d₂}, Reachable M d₁ d₂ → Reachable M d₁ (M.α⁻¹ d₂)

def CombinatorialMap.IsConnected (M : CombinatorialMap D) : Prop :=
  ∀ d₁ d₂ : D, M.Reachable d₁ d₂

namespace CombinatorialMap.Reachable

variable {M : CombinatorialMap D}

theorem trans {d₁ d₂ d₃ : D} (h1 : M.Reachable d₁ d₂) (h2 : M.Reachable d₂ d₃) : M.Reachable d₁ d₃ := by
  induction h2 with
  | refl => exact h1
  | sigma _ ih => exact sigma ih
  | alpha _ ih => exact alpha ih
  | sigma_inv _ ih => exact sigma_inv ih
  | alpha_inv _ ih => exact alpha_inv ih

theorem symm {d₁ d₂ : D} (h : M.Reachable d₁ d₂) : M.Reachable d₂ d₁ := by
  induction h
  case refl => exact refl d₁
  case sigma x y h_xy ih =>
    have h1 : M.Reachable (M.σ y) (M.σ y) := refl (M.σ y)
    have h2 : M.Reachable (M.σ y) (M.σ⁻¹ (M.σ y)) := sigma_inv (d₂ := M.σ y) h1
    have h_inv : M.Reachable (M.σ y) y := by
      have eq : M.σ⁻¹ (M.σ y) = y := Equiv.symm_apply_apply M.σ y
      rwa [eq] at h2
    exact trans h_inv ih
  case alpha x y h_xy ih =>
    have h1 : M.Reachable (M.α y) (M.α y) := refl (M.α y)
    have h2 : M.Reachable (M.α y) (M.α⁻¹ (M.α y)) := alpha_inv (d₂ := M.α y) h1
    have h_inv : M.Reachable (M.α y) y := by
      have eq : M.α⁻¹ (M.α y) = y := Equiv.symm_apply_apply M.α y
      rwa [eq] at h2
    exact trans h_inv ih
  case sigma_inv x y h_xy ih =>
    have h1 : M.Reachable (M.σ⁻¹ y) (M.σ⁻¹ y) := refl (M.σ⁻¹ y)
    have h2 : M.Reachable (M.σ⁻¹ y) (M.σ (M.σ⁻¹ y)) := sigma (d₂ := M.σ⁻¹ y) h1
    have h_inv : M.Reachable (M.σ⁻¹ y) y := by
      have eq : M.σ (M.σ⁻¹ y) = y := Equiv.apply_symm_apply M.σ y
      rwa [eq] at h2
    exact trans h_inv ih
  case alpha_inv x y h_xy ih =>
    have h1 : M.Reachable (M.α⁻¹ y) (M.α⁻¹ y) := refl (M.α⁻¹ y)
    have h2 : M.Reachable (M.α⁻¹ y) (M.α (M.α⁻¹ y)) := alpha (d₂ := M.α⁻¹ y) h1
    have h_inv : M.Reachable (M.α⁻¹ y) y := by
      have eq : M.α (M.α⁻¹ y) = y := Equiv.apply_symm_apply M.α y
      rwa [eq] at h2
    exact trans h_inv ih

end CombinatorialMap.Reachable
