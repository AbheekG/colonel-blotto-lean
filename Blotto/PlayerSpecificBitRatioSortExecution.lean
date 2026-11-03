import Blotto.PlayerSpecificSweepPreparationContract

/-! Finite-bit interpretation of the preserved stable ratio sort. Its
control width is measured once, every ratio uses actual rational tracing,
and the native array/sort backends retain all index/control/copy prices. -/
namespace Blotto.PlayerSpecificBitRatioSortExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def address (model : RationalCostModel) (measured : ℕ) : ℕ := 64*model.rat (measured+8)
def callback {n : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable n ℚ) (j : Fin n) : ℚ×ℕ :=
  let a:=v.read j
  let b:=w.read j
  let ratio:=scalar .divide a b
  (ratio.1,price model ratio.2+price model (copyRow [a,b,ratio.1])+12*A)
def prepare {n : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable n ℚ) : FixedArrayTable n ℚ×ℕ :=
  PaperIndexedArrayConstruction.run model.rat A (callback model A v w)
def run {n : ℕ} (model : RationalCostModel) (v w : FixedArrayTable n ℚ) : FixedArrayTable n (Fin n)×ℕ :=
  let measured:=PlayerSpecificWidthExecution.run model (n+1)
  let A:=address model measured.1
  let ratios:=prepare model A v w
  let sorted:=GeneralPaperNativeRepresentativeSort.run model.rat model.rat A ratios.1
  (sorted.1,measured.2+ratios.2+sorted.2+64*(n+1)*A)

theorem prepare_value {n : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable n ℚ) :
    (prepare model A v w).1=(PlayerSpecificRatioSort.prepare v w).1 := by
  unfold prepare PlayerSpecificRatioSort.prepare
  rw [PaperIndexedArrayConstruction.run_data,PaperIndexedArrayConstruction.run_data]
  rfl

theorem value {n : ℕ} (model : RationalCostModel) (v w : FixedArrayTable n ℚ) :
    (run model v w).1=(PlayerSpecificRatioSort.run v w).1 := by
  simp only [run,GeneralPaperNativeRepresentativeSort.data,prepare_value,PlayerSpecificRatioSort.data]

theorem ratio_read {n : ℕ} (model : RationalCostModel) (A : ℕ) (v w : FixedArrayTable n ℚ) (j : Fin n) :
    (prepare model A v w).1.read j=v.read j/w.read j := by
  rw [prepare_value,PlayerSpecificRatioSort.ratio_read]

end Blotto.PlayerSpecificBitRatioSortExecution
