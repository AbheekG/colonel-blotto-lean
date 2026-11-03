import Blotto.GeneralPaperIndexedListPrice

/-! Build one instruction from each retained cell and final local level.
The cell pair is read once, both endpoints are borrowed, and all record/list
writes and index/control operations are priced. Native order is preserved.
-/
namespace Blotto.GeneralPaperCellInstructionPrice
open GeneralPaperEpochCellInstructions GeneralPaperIntervalBatch
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def element {n : ℕ} (W : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ) (r : Fin n) : Instruction × ℕ :=
  let cell := cells.read r
  let amount := levels.read r
  (⟨cell.1,cell.2,amount⟩,128*W)

def run {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ) : List Instruction × ℕ :=
  GeneralPaperIndexedListPrice.run index (if bits then arrayWord W (n+2) else W) (element W cells levels)

def profile (W n : ℕ) : ℕ := n*(128*W+72*arrayWord W (n+2))+18*arrayWord W (n+2)

def arithmeticProfile (n : ℕ) : ℕ := n*200+18

theorem data {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ) :
    (run bits index W cells levels).1=GeneralPaperEpochCellInstructions.build cells levels := by
  rw [run,GeneralPaperIndexedListPrice.data]
  rfl

theorem length {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (W : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ) :
    (run bits index W cells levels).1.length=n := by
  rw [data,GeneralPaperEpochCellInstructions.build_length]

theorem bit_work {n : ℕ} (W : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ) :
    (run true (fun w => w) W cells levels).2≤profile W n := by
  apply GeneralPaperIndexedListPrice.work (fun w => w) (arrayWord W (n+2)) (128*W) (element W cells levels)
  · exact GeneralPaperSummaryArrayControls.array_word_positive W (n+2)
  · intro r hr
    have hw := binaryWordWidth_mono (show r+1≤n+2+1 by omega)
    unfold arrayWord
    omega
  · intro r
    exact Nat.le_refl _

theorem arithmetic_work {n : ℕ} (cells : Cells n) (levels : FixedArrayTable n ℕ) :
    (run false (fun _ => 1) 1 cells levels).2≤arithmeticProfile n := by
  exact GeneralPaperIndexedListPrice.work (fun _ => 1) 1 128 (element 1 cells levels)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)

theorem member_bounds {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (W U G : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ)
    (hCells : ∀ r,(cells.read r).1≤U ∧ (cells.read r).2≤U) (hLevels : ∀ r,levels.read r≤G)
    (entry : Instruction) (hEntry : entry∈(run bits index W cells levels).1) :
    entry.lo≤U ∧ entry.hi≤U ∧ entry.amount≤G := by
  rw [data] at hEntry
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp hEntry
  rw [←hr]
  exact ⟨(hCells r).1,(hCells r).2,hLevels r⟩

theorem same_data {n : ℕ} (W : ℕ) (cells : Cells n) (levels : FixedArrayTable n ℕ) :
    (run true (fun w => w) W cells levels).1=(run false (fun _ => 1) 1 cells levels).1 := by rw [data,data]

end Blotto.GeneralPaperCellInstructionPrice
