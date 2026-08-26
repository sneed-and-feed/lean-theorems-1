import Formalization.FriendshipTheorem.Basic
import Formalization.FriendshipTheorem.Politician
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Matrix Powers, Closed Walks, and Elimination of Regular Friendship Graphs

This module formalizes the algebraic and group-theoretic argument eliminating the
existence of $k$-regular friendship graphs with $k \ge 3$:
1. **Walk Counts & Matrix Powers**: `walkCount G u v m` counts walks of length $m$ from $u$ to $v$.
   For a $k$-regular friendship graph, $A^2 = (k - 1)I + J$, and mod $p$ (where $p \mid (k-1)$),
   the entries of $A^m$ are identically 1 for all $m \ge 2$.
2. **Closed Walk Group Action**: The cyclic $p$-group $\mathbb{Z}/p\mathbb{Z}$ acts by cyclic shift
   on closed walks of prime length $p$. Since $p \ge 3$ and $G$ has no self-loops, there are
   no fixed points, so the total number of closed walks is divisible by $p$.
3. **Trace Contradiction**: The trace of $A^p$ mod $p$ equals $|V| \equiv 1 \pmod p$, but the total
   closed walk count is $0 \pmod p$, yielding $0 \equiv 1 \pmod p$, which is impossible.

## Main Theorems
* `walkCount_zmod`: In a $k$-regular friendship graph with $k \equiv 1 \pmod p$, every walk count of
  length $m \ge 2$ is $1 \pmod p$.
* `card_closedWalk_mod_p`: The number of closed walks of prime length $p \ge 3$ is $0 \pmod p$.
* `no_regular_friendship_graph_ge_three`: There are no regular friendship graphs of degree $k \ge 3$.
-/

namespace FriendshipTheorem

set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of walks of length `m` from `u` to `v` in `G`. -/
def walkCount (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ → ℕ
  | 0 => if u = v then 1 else 0
  | m + 1 => ∑ x ∈ G.neighborFinset u, walkCount G x v m

lemma walkCount_one (u v : V) :
    walkCount G u v 1 = if v ∈ G.neighborFinset u then (1 : ℕ) else 0 := by
  simp [walkCount]

lemma walkCount_two (h_friend : HasFriendshipProperty G) (k : ℕ)
    (h_reg : ∀ v : V, G.degree v = k) (u v : V) :
    walkCount G u v 2 = if u = v then k else 1 := by
  dsimp [walkCount]
  have h1 (x : V) : walkCount G x v 1 = if x ∈ G.neighborFinset v then (1 : ℕ) else 0 := by
    rw [walkCount_one]
    by_cases hxv : v ∈ G.neighborFinset x
    · rw [if_pos hxv]
      rw [G.mem_neighborFinset] at hxv
      have : x ∈ G.neighborFinset v := by rwa [G.mem_neighborFinset, G.adj_comm]
      rw [if_pos this]
    · rw [if_neg hxv]
      have : x ∉ G.neighborFinset v := by
        intro h
        rw [G.mem_neighborFinset, G.adj_comm] at h
        exact hxv (by rwa [G.mem_neighborFinset])
      rw [if_neg this]
  have h2 : (∑ x ∈ G.neighborFinset u, walkCount G x v 1) =
      ∑ x ∈ G.neighborFinset u, if x ∈ G.neighborFinset v then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    exact h1 x
  show (∑ x ∈ G.neighborFinset u, walkCount G x v 1) = if u = v then k else 1
  rw [h2]
  have h3 : (∑ x ∈ G.neighborFinset u, if x ∈ G.neighborFinset v then (1 : ℕ) else 0) =
      (G.neighborFinset u ∩ G.neighborFinset v).card := by
    rw [Finset.sum_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
    rfl
  rw [h3]
  by_cases huv : u = v
  · subst huv
    rw [if_pos rfl, Finset.inter_self, show (G.neighborFinset u).card = k from h_reg u]
  · rw [if_neg huv, h_friend u v huv]

lemma walkCount_zmod (h_friend : HasFriendshipProperty G) (k : ℕ)
    (h_reg : ∀ v : V, G.degree v = k) {p : ℕ} (hpk : (k : ZMod p) = 1)
    (m : ℕ) (hm : 2 ≤ m) (u v : V) :
    (walkCount G u v m : ZMod p) = 1 := by
  induction' m, hm using Nat.le_induction with m hm ih generalizing u
  · rw [walkCount_two h_friend k h_reg]
    by_cases huv : u = v
    · rw [if_pos huv, hpk]
    · rw [if_neg huv]
      push_cast
      rfl
  · dsimp [walkCount]
    push_cast
    have : (∑ x ∈ G.neighborFinset u, (walkCount G x v m : ZMod p)) =
        ∑ x ∈ G.neighborFinset u, 1 := by
      apply Finset.sum_congr rfl
      intro x _
      exact ih x
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_card : (G.neighborFinset u).card = k := h_reg u
    rw [h_card, hpk]

/-- Sequence of vertices representing a walk of length `m` from `u` to `v`. -/
def WalkVec (G : SimpleGraph V) (u v : V) (m : ℕ) : Type _ :=
  { w : Fin (m + 1) → V // w 0 = u ∧ w (Fin.last m) = v ∧ ∀ j : Fin m, G.Adj (w j.castSucc) (w j.succ) }

instance (u v : V) (m : ℕ) : Fintype (WalkVec G u v m) := by
  classical exact Subtype.fintype _

def walkVecZeroEquiv (u v : V) (h : u = v) : WalkVec G u v 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨fun _ => u, rfl, h, fun j => j.elim0⟩
  left_inv := by
    rintro ⟨w, hw0, hw_last, _⟩
    apply Subtype.ext
    ext ⟨i, hi⟩
    have : i = 0 := by omega
    subst this
    exact hw0.symm
  right_inv := by
    rintro ⟨⟩
    rfl

def walkVecSuccEquiv (u v : V) (m : ℕ) :
    WalkVec G u v (m + 1) ≃ Σ (x : G.neighborFinset u), WalkVec G x.1 v m where
  toFun := fun ⟨w, hw0, hw_last, hw_adj⟩ =>
    ⟨⟨w 1, by
      rw [G.mem_neighborFinset]
      have hadj := hw_adj 0
      have h0 : (0 : Fin (m + 1)).castSucc = 0 := rfl
      have h1 : (0 : Fin (m + 1)).succ = 1 := rfl
      rw [h0, h1, hw0] at hadj
      exact hadj⟩,
     ⟨Fin.tail w,
      rfl,
      by
        show w (Fin.last m).succ = v
        have : (Fin.last m).succ = Fin.last (m + 1) := by ext; simp [Fin.last]
        rw [this, hw_last],
      fun j => by
        show G.Adj (w j.castSucc.succ) (w j.succ.succ)
        have h1 : j.castSucc.succ = (j.succ : Fin (m + 1)).castSucc := by ext; simp
        have h2 : j.succ.succ = (j.succ : Fin (m + 1)).succ := by ext; simp
        rw [h1, h2]
        exact hw_adj j.succ⟩⟩
  invFun := fun ⟨⟨x, hx⟩, ⟨p, hp0, hp_last, hp_adj⟩⟩ =>
    ⟨Fin.cons u p,
     by rw [Fin.cons_zero],
     by
       have : (Fin.last (m + 1) : Fin (m + 2)) = (Fin.last m).succ := by ext; simp [Fin.last]
       rw [this, Fin.cons_succ, hp_last],
     fun j => by
       cases j using Fin.cases with
       | zero =>
         have h0 : (0 : Fin (m + 1)).castSucc = 0 := rfl
         have h1 : (0 : Fin (m + 1)).succ = (1 : Fin (m + 2)) := rfl
         rw [h0, h1, Fin.cons_zero]
         rw [show (1 : Fin (m + 2)) = (0 : Fin (m + 1)).succ from rfl, Fin.cons_succ, hp0]
         rw [G.mem_neighborFinset] at hx
         exact hx
       | succ j' =>
         have h1 : (j'.succ : Fin (m + 1)).castSucc = j'.castSucc.succ := by ext; simp
         have h2 : (j'.succ : Fin (m + 1)).succ = j'.succ.succ := by ext; simp
         rw [h1, h2, Fin.cons_succ, Fin.cons_succ]
         exact hp_adj j'⟩
  left_inv := by
    rintro ⟨w, hw0, hw_last, hw_adj⟩
    apply Subtype.ext
    ext i
    cases i using Fin.cases with
    | zero => simp [hw0]
    | succ j => simp [Fin.tail]
  right_inv := by
    rintro ⟨x, ⟨p, hp0, hp_last, hp_adj⟩⟩
    have hx_adj : G.Adj u (p 0) := by
      have : p 0 = x.1 := hp0
      rw [this]
      have hx2 := x.2
      rw [G.mem_neighborFinset] at hx2
      exact hx2
    have hx : (⟨p 0, by rw [G.mem_neighborFinset]; exact hx_adj⟩ : G.neighborFinset u) = x := Subtype.ext hp0
    cases hx
    rfl

lemma card_walkVec (u v : V) (m : ℕ) :
    Fintype.card (WalkVec G u v m) = walkCount G u v m := by
  induction' m with m ih generalizing u
  · dsimp [walkCount]
    by_cases huv : u = v
    · subst huv
      rw [if_pos rfl]
      have : WalkVec G u u 0 ≃ Unit := walkVecZeroEquiv u u rfl
      rw [Fintype.card_congr this, Fintype.card_unit]
    · rw [if_neg huv]
      have : IsEmpty (WalkVec G u v 0) := ⟨by
        rintro ⟨w, hw0, hw_last, _⟩
        have : u = v := hw0.symm.trans hw_last
        exact huv this⟩
      exact Fintype.card_eq_zero
  · dsimp [walkCount]
    rw [Fintype.card_congr (walkVecSuccEquiv u v m)]
    rw [Fintype.card_sigma]
    have : (∑ (x : G.neighborFinset u), Fintype.card (WalkVec G x.1 v m)) =
        ∑ x ∈ G.neighborFinset u, walkCount G x v m := by
      rw [← Finset.sum_attach (G.neighborFinset u) (fun x => walkCount G x v m)]
      apply Finset.sum_congr rfl
      intro ⟨x, hx⟩ _
      exact ih x
    exact this

/-- Closed walks of length `p` in `G`. -/
def ClosedWalk (G : SimpleGraph V) (p : ℕ) [NeZero p] : Type _ :=
  { w : ZMod p → V // ∀ i : ZMod p, G.Adj (w i) (w (i + 1)) }

instance (p : ℕ) [NeZero p] : Fintype (ClosedWalk G p) := by
  classical exact Subtype.fintype _

def closedWalkShift (G : SimpleGraph V) {p : ℕ} [NeZero p] (s : ZMod p) (w : ClosedWalk G p) : ClosedWalk G p :=
  ⟨fun i => w.1 (i + s), fun i => by
    have hw := w.2 (i + s)
    have : i + s + 1 = i + 1 + s := by ring
    rw [this] at hw
    exact hw⟩

instance {p : ℕ} [NeZero p] : SMul (Multiplicative (ZMod p)) (ClosedWalk G p) where
  smul g w := closedWalkShift G (Multiplicative.toAdd g) w

instance {p : ℕ} [NeZero p] : MulAction (Multiplicative (ZMod p)) (ClosedWalk G p) where
  one_smul w := Subtype.ext (funext fun i => by
    change w.1 (i + 0) = w.1 i
    rw [add_zero])
  mul_smul g1 g2 w := Subtype.ext (funext fun i => by
    change w.1 (i + (Multiplicative.toAdd g1 + Multiplicative.toAdd g2)) = w.1 (i + Multiplicative.toAdd g1 + Multiplicative.toAdd g2)
    rw [add_assoc])

lemma closedWalk_fixedPoints_empty {p : ℕ} [Fact p.Prime] (_hp : 3 ≤ p) :
    IsEmpty (MulAction.fixedPoints (Multiplicative (ZMod p)) (ClosedWalk G p)) := by
  constructor
  intro ⟨w, hw⟩
  have h_fix : Multiplicative.ofAdd (1 : ZMod p) • w = w := hw (Multiplicative.ofAdd 1)
  have h_ext : (Multiplicative.ofAdd (1 : ZMod p) • w : ClosedWalk G p).1 = w.1 := by rw [h_fix]
  have h0 : (w.1 (0 + 1) : V) = w.1 0 := congr_fun h_ext 0
  rw [zero_add] at h0
  have hadj := w.2 0
  rw [zero_add, h0] at hadj
  exact hadj.ne rfl

lemma card_closedWalk_mod_p {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) :
    (Fintype.card (ClosedWalk G p) : ZMod p) = 0 := by
  have h_pg : IsPGroup p (Multiplicative (ZMod p)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, pow_one]
  have h_modeq := h_pg.card_modEq_card_fixedPoints (ClosedWalk G p)
  have h_empty : IsEmpty (MulAction.fixedPoints (Multiplicative (ZMod p)) (ClosedWalk G p)) :=
    closedWalk_fixedPoints_empty hp
  have h_zero : Nat.card (MulAction.fixedPoints (Multiplicative (ZMod p)) (ClosedWalk G p)) = 0 :=
    Nat.card_eq_zero.mpr (Or.inl h_empty)
  rw [h_zero] at h_modeq
  rw [Nat.ModEq, Nat.zero_mod] at h_modeq
  have h_dvd : p ∣ Fintype.card (ClosedWalk G p) := by
    rw [Nat.card_eq_fintype_card] at h_modeq
    exact Nat.dvd_of_mod_eq_zero h_modeq
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mpr h_dvd

def CW_at (G : SimpleGraph V) (p : ℕ) [NeZero p] (v : V) : Type _ :=
  { w : ZMod p → V // w 0 = v ∧ ∀ i : ZMod p, G.Adj (w i) (w (i + 1)) }

instance (p : ℕ) [NeZero p] (v : V) : Fintype (CW_at G p v) := by
  classical exact Subtype.fintype _

def closedWalkSigmaEquiv (p : ℕ) [NeZero p] :
    ClosedWalk G p ≃ Σ v : V, CW_at G p v where
  toFun w := ⟨w.1 0, ⟨w.1, rfl, w.2⟩⟩
  invFun := fun ⟨v, ⟨w, hw0, hw_adj⟩⟩ => ⟨w, hw_adj⟩
  left_inv := fun w => Subtype.ext rfl
  right_inv := by
    rintro ⟨v, ⟨w, rfl, hw_adj⟩⟩
    rfl

def cwAtEquivWalkVec (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (v : V) :
    CW_at G p v ≃ WalkVec G v v p where
  toFun := fun ⟨cw, hw0, hw_adj⟩ =>
    ⟨fun j => cw (j.1 : ZMod p),
     by
       have : ((0 : Fin (p + 1)).1 : ZMod p) = 0 := by simp
       show cw ((0 : Fin (p + 1)).1 : ZMod p) = v
       rw [this, hw0],
     by
       have : ((Fin.last p : Fin (p + 1)).1 : ZMod p) = 0 := by simp [Fin.last]
       show cw ((Fin.last p : Fin (p + 1)).1 : ZMod p) = v
       rw [this, hw0],
     fun j => by
       have hj_cs : (j.castSucc : Fin (p + 1)).1 = (j.1 : ℕ) := rfl
       have hj_s : ((j.succ : Fin (p + 1)).1 : ZMod p) = (j.1 : ZMod p) + 1 := by
         have : (j.succ : Fin (p + 1)).1 = j.1 + 1 := rfl
         rw [this]
         push_cast
         rfl
       have hadj := hw_adj (j.1 : ZMod p)
       show G.Adj (cw ((j.castSucc : Fin (p + 1)).1 : ZMod p)) (cw ((j.succ : Fin (p + 1)).1 : ZMod p))
       rw [hj_cs, hj_s]
       exact hadj⟩
  invFun := fun ⟨w, hw0, hw_last, hw_adj⟩ =>
    ⟨fun (i : ZMod p) => w ⟨i.val, by have := ZMod.val_lt i; omega⟩,
     by
       have h0 : (⟨(0 : ZMod p).val, by have := ZMod.val_lt (0 : ZMod p); omega⟩ : Fin (p + 1)) = 0 := by
         ext; simp [ZMod.val_zero]
       show w ⟨(0 : ZMod p).val, by have := ZMod.val_lt (0 : ZMod p); omega⟩ = v
       rw [h0, hw0],
     fun (i : ZMod p) => by
       have hp_pos : 0 < p := Nat.Prime.pos Fact.out
       by_cases hi : i.val + 1 < p
       · have h_val_add : (i + 1).val = i.val + 1 := by
           rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by omega)]
         have hadj := hw_adj ⟨i.val, by omega⟩
         have h1 : (⟨i.val, by have := ZMod.val_lt i; omega⟩ : Fin (p + 1)) =
             (⟨i.val, by omega⟩ : Fin p).castSucc := rfl
         have h2 : (⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩ : Fin (p + 1)) =
             (⟨i.val, by omega⟩ : Fin p).succ := by ext; simp [h_val_add]
         show G.Adj (w ⟨i.val, by have := ZMod.val_lt i; omega⟩) (w ⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩)
         rw [h1, h2]
         exact hadj
       · have hi_eq : i.val = p - 1 := by
           have := ZMod.val_lt i
           omega
         have hp_sub : p - 1 + 1 = p := by omega
         have hi1_val : (i + 1).val = 0 := by
           rw [ZMod.val_add, ZMod.val_one, hi_eq]
           rw [hp_sub, Nat.mod_self]
         have hadj := hw_adj ⟨p - 1, by omega⟩
         have h1 : (⟨i.val, by have := ZMod.val_lt i; omega⟩ : Fin (p + 1)) =
             (⟨p - 1, by omega⟩ : Fin p).castSucc := by ext; simp [hi_eq]
         have h2 : (⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩ : Fin (p + 1)) = 0 := by
           ext; simp [hi1_val]
         have h_last : (⟨p - 1, by omega⟩ : Fin p).succ = Fin.last p := by ext; simp [Fin.last]; omega
         show G.Adj (w ⟨i.val, by have := ZMod.val_lt i; omega⟩) (w ⟨(i + 1).val, by have := ZMod.val_lt (i + 1); omega⟩)
         rw [h1, h2, hw0]
         have h_adj' : G.Adj (w (⟨p - 1, by omega⟩ : Fin p).castSucc) (w (⟨p - 1, by omega⟩ : Fin p).succ) := hadj
         rw [h_last, hw_last] at h_adj'
         exact h_adj'⟩
  left_inv := by
    rintro ⟨cw, hw0, hw_adj⟩
    apply Subtype.ext
    ext (i : ZMod p)
    dsimp
    have : ((i.val : ℕ) : ZMod p) = i := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    exact congr_arg cw this
  right_inv := by
    rintro ⟨w, hw0, hw_last, hw_adj⟩
    apply Subtype.ext
    ext ⟨idx, hidx⟩
    dsimp
    by_cases hj_lt : idx < p
    · have : (⟨((idx : ZMod p).val : ℕ), by have := ZMod.val_lt (idx : ZMod p); omega⟩ : Fin (p + 1)) =
          ⟨idx, hidx⟩ := by
        ext
        simp [ZMod.val_natCast_of_lt hj_lt]
      rw [this]
    · have h_eq : idx = p := by omega
      have h_val_p : (((idx : ZMod p).val : ℕ) : ℕ) = 0 := by
        have : (idx : ZMod p) = (p : ZMod p) := by rw [h_eq]
        rw [this, CharP.cast_eq_zero (ZMod p) p, ZMod.val_zero]
      have h_fin_zero : (⟨((idx : ZMod p).val : ℕ), by have := ZMod.val_lt (idx : ZMod p); omega⟩ : Fin (p + 1)) = 0 := by
        ext
        exact h_val_p
      rw [h_fin_zero, hw0]
      have h_fin_last : (⟨idx, hidx⟩ : Fin (p + 1)) = Fin.last p := by
        ext
        simp [Fin.last, h_eq]
      rw [h_fin_last, hw_last]

def closedWalkEquiv (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ClosedWalk G p ≃ Σ v : V, WalkVec G v v p :=
  (closedWalkSigmaEquiv p).trans (Equiv.sigmaCongrRight (fun v => cwAtEquivWalkVec p hp v))

/-- There are no regular friendship graphs of degree `k ≥ 3`. -/
lemma no_regular_friendship_graph_ge_three (h_friend : HasFriendshipProperty G)
    (k : ℕ) (hk : 3 ≤ k) (h_reg : ∀ v : V, G.degree v = k) (h_card : 3 ≤ Fintype.card V) :
    False := by
  have h_nonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u₀⟩ := h_nonempty
  have h_even_deg := even_degree_of_friendship h_friend u₀
  rw [h_reg u₀] at h_even_deg
  have hk_even : Even k := h_even_deg
  have hk_ge4 : 4 ≤ k := by
    obtain ⟨c, hc⟩ := hk_even
    omega
  let p := (k - 1).minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ (k - 1) := Nat.minFac_dvd (k - 1)
  have hp_ge3 : 3 ≤ p := by
    have : p ≠ 2 := by
      intro hp2
      have hp2_dvd : 2 ∣ (k - 1) := hp2 ▸ hp_dvd
      obtain ⟨c, hc⟩ := hk_even
      omega
    have : 2 ≤ p := hp_prime.two_le
    omega
  have hp_fact : Fact p.Prime := ⟨hp_prime⟩
  have hpk : (k : ZMod p) = 1 := by
    have : ((k - 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (k - 1)).mpr hp_dvd
    have h_k_eq : k = (k - 1) + 1 := by omega
    rw [h_k_eq, Nat.cast_add, this, zero_add, Nat.cast_one]
  have h_card_V_zmod : (Fintype.card V : ZMod p) = 1 := by
    have h_card_V := card_V_eq_k_mul_k_sub_one_add_one h_friend k h_reg h_card
    rw [h_card_V]
    push_cast
    have : ((k - 1 : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p (k - 1)).mpr hp_dvd
    rw [this, mul_zero, zero_add]
  have h_sum_walk : (∑ v : V, (walkCount G v v p : ZMod p)) = 1 := by
    have h_each (v : V) : (walkCount G v v p : ZMod p) = 1 :=
      walkCount_zmod h_friend k h_reg hpk p (by omega) v v
    have : (∑ v : V, (walkCount G v v p : ZMod p)) = ∑ v : V, 1 := by
      apply Finset.sum_congr rfl
      intro v _
      exact h_each v
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.card : ZMod p) = (Fintype.card V : ZMod p) := rfl
    rw [this, h_card_V_zmod]
  have h_cw_zero : (Fintype.card (ClosedWalk G p) : ZMod p) = 0 :=
    card_closedWalk_mod_p hp_ge3
  have h_card_eq : Fintype.card (ClosedWalk G p) = Fintype.card (Σ v : V, WalkVec G v v p) :=
    Fintype.card_congr (closedWalkEquiv p hp_ge3)
  have h_sigma_card : Fintype.card (Σ v : V, WalkVec G v v p) = ∑ v : V, walkCount G v v p := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro v _
    exact card_walkVec v v p
  have h_cw_eq_sum : (Fintype.card (ClosedWalk G p) : ZMod p) = ∑ v : V, (walkCount G v v p : ZMod p) := by
    rw [h_card_eq, h_sigma_card]
    push_cast
    rfl
  rw [h_cw_zero, h_sum_walk] at h_cw_eq_sum
  have h_contra : (0 : ZMod p) = (1 : ZMod p) := h_cw_eq_sum
  have h_one_zero : ((1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_one]
    exact h_contra.symm
  have h_p_dvd_one : p ∣ 1 := (CharP.cast_eq_zero_iff (ZMod p) p 1).mp h_one_zero
  have : p ≤ 1 := Nat.le_of_dvd (by omega) h_p_dvd_one
  omega

end FriendshipTheorem
