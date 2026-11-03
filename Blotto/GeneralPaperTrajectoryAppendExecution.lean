import Blotto.GeneralPaperForestInitialPrice

/-! Append each new epoch row by one read and one reference push. The old
trajectory is retained; no old row is traversed or copied by this loop. -/
namespace Blotto.GeneralPaperTrajectoryAppendExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def pushPrefix {α : Type*} (bits : Bool) (index : ℕ → ℕ) (W capacity : ℕ) (chunk first : Array α) :
    (count : ℕ) → count≤chunk.size → Array α × ℕ
  | 0,_ => (first,GeneralPaperIntegerWordPrice.compare index 0 0+64*(if bits then arrayWord W (capacity+2) else W))
  | count+1,h =>
    let A := if bits then arrayWord W (capacity+2) else W
    let previous := pushPrefix bits index W capacity chunk first count (by omega)
    (previous.1.push (chunk[count]'(by omega)),previous.2+64*A+
      PaperIndexedArrayConstruction.stepWork index A previous.1.size+GeneralPaperLocalEpochExecution.control index A (count+1))

theorem prefix_data {α : Type*} (bits : Bool) (index : ℕ → ℕ) (W capacity : ℕ) (chunk first : Array α)
    (count : ℕ) (h : count≤chunk.size) : (pushPrefix bits index W capacity chunk first count h).1=
      GeneralPaperCatalogueTrajectoryAppend.pushPrefix chunk first count h := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [pushPrefix,GeneralPaperCatalogueTrajectoryAppend.pushPrefix,ih]

theorem prefix_size {α : Type*} (bits : Bool) (index : ℕ → ℕ) (W capacity : ℕ) (chunk first : Array α)
    (count : ℕ) (h : count≤chunk.size) : (pushPrefix bits index W capacity chunk first count h).1.size=first.size+count := by
  rw [prefix_data,GeneralPaperCatalogueTrajectoryAppend.pushPrefix_size]

def run {α : Type*} (bits : Bool) (index : ℕ → ℕ) (W capacity : ℕ) (first chunk : Array α) : Array α × ℕ :=
  let pushed := pushPrefix bits index W capacity chunk first chunk.size le_rfl
  (pushed.1,pushed.2+64*W)

theorem data {α : Type*} (bits : Bool) (index : ℕ → ℕ) (W capacity : ℕ) (first chunk : Array α) :
    (run bits index W capacity first chunk).1=GeneralPaperCatalogueTrajectoryAppend.append first chunk :=
  prefix_data bits index W capacity chunk first chunk.size le_rfl

theorem prefix_capacity {α : Type*} (bits : Bool) (index : ℕ → ℕ) (W capacity : ℕ) (chunk first : Array α)
    (count : ℕ) (h : count≤chunk.size) (hTotal : first.size+chunk.size≤capacity) :
    (pushPrefix bits index W capacity chunk first count h).1.size≤capacity := by rw [prefix_size]; omega

end Blotto.GeneralPaperTrajectoryAppendExecution
