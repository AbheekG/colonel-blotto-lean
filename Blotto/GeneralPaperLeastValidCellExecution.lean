import Blotto.GeneralPaperLeastValidPrice

/-! The guarded half-open cell wrapper. Empty cells stop before subtracting
one from hi; nonempty cells call the complete least-valid lookup once.
Range subtraction, native counter addition, guards and writes are priced.
-/
namespace Blotto.GeneralPaperLeastValidCellExecution
open GeneralPaperCodeAlphabet
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperCodeMinimumScan.Result × ℕ :=
  let common := GeneralPaperIntegerWordPrice.compare (primitive bits model) lo hi+64*W
  if lo<hi then
    let found := GeneralPaperLeastValidExecution.run bits model W a response lo (hi-1)
    (⟨found.1.selected,found.1.work+16⟩,common+found.2+
      GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a-b) hi 1+
      GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a+b) found.1.work 16+64*W)
  else (⟨none,16⟩,common+64*W)

theorem data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run bits model W a response lo hi).1=GeneralPaperLeastValidCell.run a response lo hi := by
  unfold run GeneralPaperLeastValidCell.run
  split
  · dsimp only
    rw [GeneralPaperLeastValidExecution.data]
  · rfl

theorem best (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperOrderedMinimum.Best (GeneralPaperLeastValidCell.Possible a response lo hi)
      (run bits model W a response lo hi).1.selected := by
  rw [data]
  exact GeneralPaperLeastValidCell.run_best a response lo hi

theorem empty_none (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (hEmpty : hi≤lo) : (run bits model W a response lo hi).1.selected=none := by
  rw [data]
  exact GeneralPaperLeastValidCell.empty_none a response lo hi hEmpty

theorem resource_domination (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ)
    (entry : Entry) (hSome : (run bits model W a response lo hi).1.selected=some entry)
    (code : ℕ) (choice : Choice) (hLo : lo≤code) (hHi : code<hi)
    (hDecode : (GeneralPaperCodeDecode.decode a response code).choice=some choice) : entry.predecessor.tag≤choice.tag := by
  rw [data] at hSome
  exact GeneralPaperLeastValidResource.cell_domination a response lo hi entry hSome code choice hLo hHi hDecode

end Blotto.GeneralPaperLeastValidCellExecution
