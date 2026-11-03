import Blotto.GeneralPaperCodeScanPrice

/-! One starting split, one five-candidate constructor and one minimum
scan. Native work additions are accumulated in the returned Result itself;
no decoder, constructor or annotation-sum replay is executed.
-/
namespace Blotto.GeneralPaperLeastValidExecution
open GeneralPaperCodeAlphabet
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def additions (price : ℕ → ℕ) (splitWork scanWork : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) splitWork scanWork+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (splitWork+scanWork) 32

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperCodeMinimumScan.Result × ℕ :=
  let common := GeneralPaperCodeDecodeExecution.control (primitive bits model) W a lo
  if lo≤4*a.C then
    let split := GeneralPaperCodeSplitExecution.run bits model W lo a.lambda
    let points := GeneralPaperLeastValidPointsPrice.run (primitive bits model) W split.1.bucket
    let found := GeneralPaperCodeScanExecution.scan bits model W a response lo hi points.1
    (⟨found.1.selected,split.1.work+found.1.work+32⟩,
      common+split.2+points.2+found.2+additions (primitive bits model) split.1.work found.1.work+64*W)
  else (⟨none,16⟩,common+64*W)

theorem data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run bits model W a response lo hi).1=GeneralPaperLeastValid.run a response lo hi := by
  unfold run GeneralPaperLeastValid.run
  split
  · dsimp only
    rw [GeneralPaperCodeSplitExecution.data,GeneralPaperLeastValidPointsPrice.data,GeneralPaperCodeScanExecution.scan_data]
  · rfl

theorem best (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    GeneralPaperOrderedMinimum.Best (GeneralPaperCodeMinimumScan.Possible a response lo hi)
      (run bits model W a response lo hi).1.selected := by
  rw [data]
  exact GeneralPaperLeastValid.run_best a response lo hi

end Blotto.GeneralPaperLeastValidExecution
