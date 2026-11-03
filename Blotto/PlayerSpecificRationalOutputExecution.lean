import Blotto.PlayerSpecificOutputFloorExecution
import Blotto.PlayerSpecificRationalOutput

/-! Complete measured rational array emission calls the actual dyadic
floor once per original coordinate and charges all input/output rows,
indices and the returned array. Its rational return is exactly native. -/
namespace Blotto.PlayerSpecificRationalOutputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data)
    (result : FixedArrayTable N ℚ) (P : ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([root.polynomial,[root.interval.lo,root.interval.hi]]++
      List.ofFn y.read++List.ofFn (fun j => [result.read j]))
    ([N,P,1]++List.range N++List.range N)

def run {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (P : ℕ) :
    FixedArrayTable N ℚ×ℕ :=
  let measured:=FixedArrayTable.ofFn (fun j => PlayerSpecificOutputFloorExecution.round root (y.read j) P)
  let result:=FixedArrayTable.ofFn (fun j => (measured.read j).1)
  (result,(∑ j : Fin N,(measured.read j).2)+price RationalCostModel.schoolbook (frame root y result P))

theorem value {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (P : ℕ) :
    (run root y P).1=PlayerSpecificRationalOutput.run root y P := by
  apply congrArg FixedArrayTable.ofFn
  funext j
  simp only [FixedArrayTable.read_ofFn,PlayerSpecificOutputFloorExecution.round_value]

end Blotto.PlayerSpecificRationalOutputExecution
