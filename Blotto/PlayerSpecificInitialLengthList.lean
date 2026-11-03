import Blotto.PlayerSpecificAlgebraicInitialVectorContract

/-! Actual cached length-list materialization. Each stored field is read
once into an indexed reference array, whose backwards tail loop returns
the length list. No initial-data routine is called again. -/
namespace Blotto.PlayerSpecificInitialLengthList
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def callback {N : ℕ} (model : RationalCostModel) (A : ℕ) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (j : Fin N) : Data×ℕ :=
  let row:=(p.rows.read j).length
  (row,price model (copyRow row)+12*A)

def run {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) : List Data×ℕ :=
  let measured:=PlayerSpecificWidthExecution.run model (N+1)
  let A:=PlayerSpecificBitRatioSortExecution.address model measured.1
  let table:=PaperIndexedArrayConstruction.run model.rat A (callback model A p)
  (StoredArrayReferenceList.list table.1.data,measured.2+table.2+
    StoredArrayReferenceList.work model.rat A table.1.data.size+64*(N+1)*A+price model [.control N,.control 0])

theorem value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) :
    (run model p).1=PlayerSpecificMinimumContract.lengths p := by
  simp only [run,StoredArrayReferenceList.list_data,PaperIndexedArrayConstruction.run_data,
    FixedArrayTable.ofFn,Array.toList_ofFn,callback,PlayerSpecificMinimumContract.lengths]

theorem reference_work (model : RationalCostModel) (N : ℕ) :
    StoredArrayReferenceList.work model.rat
      (PlayerSpecificBitRatioSortExecution.address model (PlayerSpecificWidthExecution.run model (N+1)).1) N≤
      12*(N+1)*PlayerSpecificBitRatioSortExecution.address model (PlayerSpecificWidthExecution.run model (N+1)).1 := by
  rw [PlayerSpecificWidthExecution.value]
  let A:=PlayerSpecificBitRatioSortExecution.address model (binaryWordWidth (N+1))
  have hA : 1≤A := by
    have hh:=model.word_le (binaryWordWidth (N+1)+8)
    dsimp only [A,PlayerSpecificBitRatioSortExecution.address]
    omega
  have hword (n : ℕ) (hn : n≤N) : model.rat (binaryWordWidth n+1)≤A := by
    have hb : binaryWordWidth n≤binaryWordWidth (N+1) := binaryWordWidth_mono (by omega : n≤N+1)
    have hm:=model.monotone (show binaryWordWidth n+1≤binaryWordWidth (N+1)+8 by omega)
    dsimp only [A,PlayerSpecificBitRatioSortExecution.address]
    omega
  have hone : model.rat 1≤A := by
    have hm:=model.monotone (show 1≤binaryWordWidth (N+1)+8 by omega)
    dsimp only [A,PlayerSpecificBitRatioSortExecution.address]
    omega
  have loop (k : ℕ) (hk : k≤N) : StoredArrayReferenceList.work model.rat A k≤12*(k+1)*A := by
    induction k with
    | zero => simp only [StoredArrayReferenceList.work]; omega
    | succ k ih =>
      have ht:=ih (by omega)
      have hw:=hword (k+1) hk
      rw [StoredArrayReferenceList.work]
      nlinarith only [ht,hw,hA]
  exact loop N le_rfl

end Blotto.PlayerSpecificInitialLengthList
