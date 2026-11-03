import Blotto.PlayerSpecificMeasuredCodeSearch
import Blotto.PlayerSpecificAlgebraicOutputFloor

/-! One actual floor-search predicate constructs its dyadic threshold,
an exact algebraic constant, then executes the selected-root comparison.
All natural arithmetic, polynomial rows, rational threshold and controls
are charged at the source boundary. -/
namespace Blotto.PlayerSpecificOutputFloorPredicateExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (root : Candidate) (a constant : Data) (threshold : ℚ)
    (P code power numerator : ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    [root.polynomial,[root.interval.lo,root.interval.hi],a,constant,[threshold]]
    [P,code,power,numerator]

def run (root : Candidate) (a : Data) (P code : ℕ) : Bool×ℕ :=
  let model:=RationalCostModel.schoolbook
  let power:=PlayerSpecificNaturalExecution.power model 2 P
  let numerator:=PlayerSpecificNaturalExecution.binary model (fun x y => x+y) code 1
  let threshold:ℚ:=(numerator.1:ℚ)/(power.1:ℚ)
  let thresholdCost:=GeneralPaperRationalPrimitivePrice.binary model.rat
    (fun u v => u/v) (numerator.1:ℚ) (power.1:ℚ)
  let constant:=PlayerSpecificFieldCombinationContract.constant root.polynomial threshold
  let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root constant.1 a
  (!compared.1,power.2+numerator.2+thresholdCost+price model constant.2+compared.2+
    price model (frame root a constant.1 threshold P code power.1 numerator.1))

theorem value (root : Candidate) (a : Data) (P code : ℕ) :
    (run root a P code).1=PlayerSpecificAlgebraicOutputFloor.predicate root a P code := by
  simp only [run,PlayerSpecificNaturalExecution.power_value,
    PlayerSpecificNaturalExecution.binary_value,
    PlayerSpecificFieldCombinationContract.constant_value,
    PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificAlgebraicOutputFloor.predicate,
    PlayerSpecificAlgebraicOutputFloor.threshold,Nat.cast_pow,Nat.cast_ofNat]

end Blotto.PlayerSpecificOutputFloorPredicateExecution
