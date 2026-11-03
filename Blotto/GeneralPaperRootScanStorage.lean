import Blotto.GeneralPaperActualDPConstructionStorage

/-! The native right-fold root scan retains finite optional labels across
recursive calls. A callback's temporary workspace is released before the
next callback; comparison arithmetic scratch is a separate obligation. -/
namespace Blotto.GeneralPaperRootScanStorage
open GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def optionalBits {J : ℕ} (W : ℕ) : Option (Fin J) → ℕ
  | none => 32*W
  | some i => rankBits i+32*W

theorem optional_bound {J : ℕ} (W : ℕ) (value : Option (Fin J)) : optionalBits W value≤rankWord J+32*W := by
  cases value with
  | none => simp only [optionalBits]; omega
  | some i => exact Nat.add_le_add_right (rank_bound i) _

def peak {α : Type*} {J : ℕ} (index : ℕ → ℕ) (W A : ℕ) (temporary : α → ℕ)
    (evaluate : α → Option (Fin J) × ℕ) : List α → ℕ
  | [] => 64*W
  | a::rest =>
    let current := (evaluate a).1
    let later := (GeneralPaperRootScanExecution.run index A evaluate rest).1
    let picked := (GeneralPaperRootPickPrice.run index A current later).1
    max (temporary a+optionalBits W current+128*W)
      (optionalBits W current+peak index W A temporary evaluate rest+optionalBits W later+optionalBits W picked+128*W)

def profile (W J C n : ℕ) : ℕ := n*(3*rankWord J+224*W)+C+64*W

theorem bounded {α : Type*} {J : ℕ} (index : ℕ → ℕ) (W A C : ℕ)
    (temporary : α → ℕ) (evaluate : α → Option (Fin J) × ℕ) (xs : List α)
    (ht : ∀ a∈xs,temporary a≤C) : peak index W A temporary evaluate xs≤profile W J C xs.length := by
  induction xs with
  | nil => simp only [peak,profile,List.length_nil,Nat.zero_mul,Nat.zero_add]; omega
  | cons a rest ih =>
    have hc := optional_bound W (evaluate a).1
    have hl := optional_bound W (GeneralPaperRootScanExecution.run index A evaluate rest).1
    have hp := optional_bound W (GeneralPaperRootPickPrice.run index A (evaluate a).1
      (GeneralPaperRootScanExecution.run index A evaluate rest).1).1
    have ha := ht a List.mem_cons_self
    have hr := ih (fun b hb => ht b (List.mem_cons_of_mem _ hb))
    simp only [peak]
    apply max_le
    · unfold profile
      rw [List.length_cons]
      nlinarith only [hc,ha,Nat.zero_le (rest.length*(3*rankWord J+224*W))]
    · unfold profile at hr ⊢
      rw [List.length_cons]
      nlinarith only [hc,hl,hp,hr]

end Blotto.GeneralPaperRootScanStorage
