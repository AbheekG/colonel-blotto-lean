import Blotto.GeneralPaperRootPickPrice

/-! One native highest-label scan, with the same right-fold tie order.
Each callback and label comparison executes once. -/
namespace Blotto.GeneralPaperRootScanExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {α : Type*} {J : ℕ} (index : ℕ → ℕ) (W : ℕ) (evaluate : α → Option (Fin J) × ℕ) : List α → Option (Fin J) × ℕ
  | [] => (none,64*W)
  | a::rest =>
    let current := evaluate a
    let later := run index W evaluate rest
    let picked := GeneralPaperRootPickPrice.run index W current.1 later.1
    (picked.1,current.2+later.2+picked.2+64*W)

theorem data {α : Type*} {J : ℕ} (index : ℕ → ℕ) (W : ℕ) (evaluate : α → Option (Fin J) × ℕ) (xs : List α) :
    (run index W evaluate xs).1=GeneralPaperOrderedProfitRoot.scan (fun a => (evaluate a).1) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [run,GeneralPaperRootPickPrice.data,ih,GeneralPaperOrderedProfitRoot.scan]

theorem work {α : Type*} {J : ℕ} (index : ℕ → ℕ) (W A C : ℕ) (evaluate : α → Option (Fin J) × ℕ) (xs : List α)
    (hIndex : ∀ i : Fin J,index (1+binaryWordWidth i.val)≤A) (hc : ∀ a∈xs,(evaluate a).2≤C) :
    (run index W evaluate xs).2≤xs.length*(C+A+128*W)+64*W := by
  induction xs with
  | nil => change 64*W≤0*(C+A+128*W)+64*W; omega
  | cons a rest ih =>
    have ha := hc a List.mem_cons_self
    have hr := ih (fun b hb => hc b (List.mem_cons_of_mem _ hb))
    have hp := GeneralPaperRootPickPrice.work index W A (evaluate a).1 (run index W evaluate rest).1 hIndex
    change (evaluate a).2+(run index W evaluate rest).2+
      (GeneralPaperRootPickPrice.run index W (evaluate a).1 (run index W evaluate rest).1).2+64*W≤_
    rw [List.length_cons]
    nlinarith only [ha,hr,hp]

theorem arithmetic_work {α : Type*} {J : ℕ} (C : ℕ) (evaluate : α → Option (Fin J) × ℕ) (xs : List α)
    (hc : ∀ a∈xs,(evaluate a).2≤C) : (run (fun _ => 1) 1 evaluate xs).2≤xs.length*(C+129)+64 := by
  have h := work (fun _ => 1) 1 1 C evaluate xs (fun _ => Nat.le_refl _) hc
  simpa only [Nat.mul_one] using h

end Blotto.GeneralPaperRootScanExecution
