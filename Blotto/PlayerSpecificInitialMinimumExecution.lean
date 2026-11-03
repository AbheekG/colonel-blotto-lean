import Blotto.PlayerSpecificInitialLengthListCost

/-! Actual one-time initial/minimum preparation. Each executing stage
is retained once. The global root/parameter recognizer is called once by
the original-input entry, with exact rejection preserved. -/
namespace Blotto.PlayerSpecificInitialMinimumExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared (N : ℕ) where
  initial : PlayerSpecificAlgebraicInitialVector.Result N
  minimum : PlayerSpecificMinimumSearch.Result

def frame (N : ℕ) (quantum : ℚ) (exponent : ℕ) : Trace :=
  copyRow [quantum]++[.control N,.control exponent,.control 1]

def accept {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) : Prepared N×ℕ :=
  let initial:=PlayerSpecificAlgebraicInitialVectorExecution.run RationalCostModel.schoolbook i r
  let lengths:=PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook initial.1
  let guard:=PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i
  let minimum:=PlayerSpecificMinimumSearch.search RationalCostModel.schoolbook r.root.polynomial r.root.interval lengths.1 guard.1 0 1
  let measured:=PlayerSpecificWidthExecution.run RationalCostModel.schoolbook (N+1)
  let A:=PlayerSpecificBitRatioSortExecution.address RationalCostModel.schoolbook measured.1
  (⟨initial.1,minimum⟩,
    initial.2+lengths.2+guard.2+minimum.work+measured.2+price RationalCostModel.schoolbook (frame N minimum.quantum minimum.exponent)+32*(N+1)*A)

def run {N : ℕ} (i : RationalPlayerSpecificInput N) : Option (Prepared N)×ℕ :=
  let described:=PlayerSpecificFiniteParameterDescription.run i
  match described.parameters with
  | none => (none,described.work+price RationalCostModel.schoolbook [.control 0])
  | some r =>
    let prepared:=accept i r
    (some prepared.1,described.work+prepared.2+price RationalCostModel.schoolbook [.control 1])

end Blotto.PlayerSpecificInitialMinimumExecution
