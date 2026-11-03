import Blotto.GeneralPaperNativeShiftPrice

/-! The actual arithmetic bin cursor: advance the next boundary by one
bin width while it is below the current odd left endpoint. The reached
advance count, rather than the numerical fuel, controls literal work. -/
namespace Blotto.GeneralPaperCircleBinAdvance
set_option autoImplicit false
set_option maxHeartbeats 1400000

structure Result where
  bin : ℕ
  next : ℕ
  advances : ℕ
  work : ℕ

def run (width position : ℕ) : ℕ → ℕ → ℕ → Result
  | 0,a,next => ⟨a,next,0,4⟩
  | fuel+1,a,next =>
    if next<position then
      let child := run width position fuel (a+1) (next+width)
      ⟨child.bin,child.next,child.advances+1,child.work+12⟩
    else ⟨a,next,0,4⟩

theorem bin_eq (width position fuel a next : ℕ) :
    (run width position fuel a next).bin=a+(run width position fuel a next).advances := by
  induction fuel generalizing a next with
  | zero => rfl
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      rw [ih]
      omega
    · rfl

theorem next_eq (width position fuel a next : ℕ) :
    (run width position fuel a next).next=next+width*(run width position fuel a next).advances := by
  induction fuel generalizing a next with
  | zero => simp only [run,Nat.mul_zero,Nat.add_zero]
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      rw [ih]
      ring
    · simp only [Nat.mul_zero,Nat.add_zero]

theorem work_eq (width position fuel a next : ℕ) :
    (run width position fuel a next).work=12*(run width position fuel a next).advances+4 := by
  induction fuel generalizing a next with
  | zero => rfl
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      rw [ih]
      omega
    · rfl

theorem advances_le (width position fuel a next : ℕ) : (run width position fuel a next).advances≤fuel := by
  induction fuel generalizing a next with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [run]
    split
    · exact Nat.add_le_add_right (ih _ _) 1
    · exact Nat.zero_le _

theorem next_invariant (width position fuel a next : ℕ) (hNext : next=(a+1)*width) :
    (run width position fuel a next).next=((run width position fuel a next).bin+1)*width := by
  rw [next_eq,bin_eq,hNext]
  ring

theorem terminal (width position fuel a next : ℕ) (hCap : position≤next+fuel*width) :
    position≤(run width position fuel a next).next := by
  induction fuel generalizing a next with
  | zero => simpa only [run,Nat.zero_mul,Nat.add_zero] using hCap
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      apply ih
      nlinarith only [hCap]
    · exact Nat.le_of_not_gt ‹¬next<position›

theorem lower (width position fuel a next : ℕ) (hNext : next=(a+1)*width) (hLower : a*width<position) :
    (run width position fuel a next).bin*width<position := by
  induction fuel generalizing a next with
  | zero => exact hLower
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      apply ih
      · nlinarith only [hNext]
      · simpa only [hNext] using ‹next<position›
    · exact hLower

theorem gap (width position fuel a next : ℕ) (hNext : next=(a+1)*width) (hLower : a*width<position)
    (hCap : position≤next+fuel*width) (hNotBoundary : ∀ b:ℕ,position≠b*width) :
    (run width position fuel a next).bin*width<position ∧
      position<((run width position fuel a next).bin+1)*width := by
  have hu := terminal width position fuel a next hCap
  rw [next_invariant width position fuel a next hNext] at hu
  exact ⟨lower width position fuel a next hNext hLower,lt_of_le_of_ne hu (hNotBoundary _)⟩

end Blotto.GeneralPaperCircleBinAdvance
