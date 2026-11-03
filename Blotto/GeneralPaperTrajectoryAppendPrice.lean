import Blotto.GeneralPaperTrajectoryAppendExecution

/-! All append controls use the retained total trajectory capacity. The
price depends on the new chunk size, not the old trajectory size. -/
namespace Blotto.GeneralPaperTrajectoryAppendPrice
open GeneralPaperTrajectoryAppendExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem step (index : ℕ → ℕ) (hMono : Monotone index) (A capacity old count : ℕ) (hA : 1≤A)
    (ho : old≤capacity) (hc : count≤capacity) (hi : index (1+binaryWordWidth (capacity+1))≤A) :
    64*A+PaperIndexedArrayConstruction.stepWork index A old+GeneralPaperLocalEpochExecution.control index A (count+1)≤256*A := by
  have hInput : binaryWordWidth (old+1)≤1+binaryWordWidth (capacity+1) := by
    have h := binaryWordWidth_mono (Nat.add_le_add_right ho 1)
    omega
  have hWord := (hMono hInput).trans hi
  have hControl := GeneralPaperLocalEpochControlPrice.control index hMono A capacity (count+1) (by omega) hi
  unfold PaperIndexedArrayConstruction.stepWork
  omega

theorem prefix_work {α : Type*} (bits : Bool) (index : ℕ → ℕ) (hMono : Monotone index) (W capacity : ℕ) (chunk first : Array α)
    (hTotal : first.size+chunk.size≤capacity)
    (hA : 1≤(if bits then arrayWord W (capacity+2) else W))
    (hIndex : index (1+binaryWordWidth (capacity+1))≤(if bits then arrayWord W (capacity+2) else W))
    (count : ℕ) (h : count≤chunk.size) :
    (pushPrefix bits index W capacity chunk first count h).2≤256*(count+1)*(if bits then arrayWord W (capacity+2) else W) := by
  let A := if bits then arrayWord W (capacity+2) else W
  induction count with
  | zero =>
    have hg := GeneralPaperLocalEpochControlPrice.guard index hMono A capacity 0 (Nat.zero_le _) hIndex
    change _+64*A≤256*(0+1)*A
    omega
  | succ count ih =>
    have hp := ih (by omega)
    have hs := step index hMono A capacity (first.size+count) count hA (by omega) (by omega) hIndex
    rw [pushPrefix]
    dsimp only
    rw [prefix_size]
    dsimp only [A] at hs
    nlinarith only [hp,hs]

def profile (W capacity count : ℕ) : ℕ := 256*(count+1)*arrayWord W (capacity+2)+64*W
def arithmeticProfile (count : ℕ) : ℕ := 256*(count+1)+64

theorem work {α : Type*} (W capacity : ℕ) (first chunk : Array α) (hTotal : first.size+chunk.size≤capacity) :
    (run true (fun x => x) W capacity first chunk).2≤profile W capacity chunk.size ∧
    (run false (fun _ => 1) 1 capacity first chunk).2≤arithmeticProfile chunk.size := by
  have hb := Nat.add_le_add_right (prefix_work true (fun x => x) (fun _ _ h => h) W capacity chunk first hTotal
    (GeneralPaperSummaryArrayControls.array_word_positive W (capacity+2)) (GeneralPaperLocalEpochPrice.capacity_word W capacity) _ le_rfl) (64*W)
  have hu := Nat.add_le_add_right (prefix_work false (fun _ => 1) (fun _ _ _ => Nat.le_refl _) 1 capacity chunk first hTotal
    (Nat.le_refl _) (Nat.le_refl _) _ le_rfl) (64*1)
  constructor
  · exact hb
  · simpa only [run,arithmeticProfile,Bool.false_eq_true,ite_false,Nat.mul_one] using hu

end Blotto.GeneralPaperTrajectoryAppendPrice
