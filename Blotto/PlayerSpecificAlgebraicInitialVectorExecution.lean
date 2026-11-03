import Blotto.PlayerSpecificAlgebraicInitialOriginalCost

/-! Executing vector preparation computes the inverse once, constructs
the two input arrays once and calls each initial-field routine once.
The maintained output array stores references to the returned field rows;
all callback/index/descriptor operations have explicit source prices. -/
namespace Blotto.PlayerSpecificAlgebraicInitialVectorExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

def callback {N : ℕ} (model : RationalCostModel) (A : ℕ) (root : PlayerSpecificAlgebraicCandidates.Candidate)
    (inverseScale : Data) (v w : FixedArrayTable N ℚ) (j : Fin N) : PlayerSpecificAlgebraicInitial.Result×ℕ :=
  let first:=v.read j
  let second:=w.read j
  let field:=PlayerSpecificAlgebraicInitialExecution.run model root inverseScale first second
  (field.1,field.2+price model (copyRow [first,second])+12*A)

def frame {N : ℕ} (i : RationalPlayerSpecificInput N) (inverseScale : Data) : Trace :=
  copyRow inverseScale++copyRow [i.budget]++[.control N,.control 1]

def run {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    PlayerSpecificAlgebraicInitialVector.Result N×ℕ :=
  let measured:=PlayerSpecificWidthExecution.run model (N+1)
  let A:=PlayerSpecificBitRatioSortExecution.address model measured.1
  let v:=PlayerSpecificInputArrayExecution.run model i.valuesA.weight
  let w:=PlayerSpecificInputArrayExecution.run model i.valuesB.weight
  let inverse:=PlayerSpecificAlgebraicInverseExecution.run model r.root.polynomial r.scale
  let rows:=PaperIndexedArrayConstruction.run model.rat A (callback model A r.root inverse.1 v.1 w.1)
  (⟨r,inverse.1,rows.1⟩,measured.2+v.2+w.2+inverse.2+rows.2+
    price model (frame i inverse.1)+64*(N+1)*A)

theorem value {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (run model i r).1=PlayerSpecificAlgebraicInitialVector.prepare model i r := by
  simp only [run,PaperIndexedArrayConstruction.run_data,PlayerSpecificInputArrayExecution.value,
    PlayerSpecificAlgebraicInverseExecution.value,callback,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicInitialExecution.value,PlayerSpecificAlgebraicInitialVector.prepare]

end Blotto.PlayerSpecificAlgebraicInitialVectorExecution
