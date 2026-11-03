import Blotto.PlayerSpecificAlgebraicCallerFrame

/-! A priced execution of the actual cached resource pair. Every selected
field operation is executed once. Branch rows, probability numerator and
denominator and the enclosing return/copy/control frame are retained. -/
namespace Blotto.PlayerSpecificAlgebraicPairExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (root : Candidate) (lengthA lengthB a b numerator denominator : Data)
    (result : PlayerSpecificAlgebraicPairStep.Result) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    [root.polynomial,[root.interval.lo,root.interval.hi],lengthA,lengthB,a,b,
      result.total,result.upperA,result.upperB,result.lowerA,result.lowerB,numerator,denominator,result.probability] [2,6]

def run (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data) :
    PlayerSpecificAlgebraicPairStep.Result×ℕ :=
  let total:=PlayerSpecificFieldCombination.run false root.polynomial a b
  let lowA:=PlayerSpecificAlgebraicComparisonExecution.run model root total.1 lengthA
  let lowB:=PlayerSpecificAlgebraicComparisonExecution.run model root total.1 lengthB
  let upperA:=if lowA.1 then total.1 else lengthA
  let upperB:=if lowA.1 then ([],[]) else PlayerSpecificFieldCombination.run true root.polynomial total.1 lengthA
  let lowerA:=if lowB.1 then ([],[]) else PlayerSpecificFieldCombination.run true root.polynomial total.1 lengthB
  let lowerB:=if lowB.1 then total.1 else lengthB
  let numerator:=PlayerSpecificFieldCombination.run true root.polynomial a lowerA.1
  let denominator:=PlayerSpecificFieldCombination.run true root.polynomial upperA lowerA.1
  let probability:=PlayerSpecificFieldDivisionExecution.run model root.polynomial numerator.1 denominator.1
  let result:PlayerSpecificAlgebraicPairStep.Result:=⟨total.1,upperA,upperB.1,lowerA.1,lowerB,probability.1⟩
  (result,price model total.2+lowA.2+lowB.2+price model upperB.2+price model lowerA.2+
    price model numerator.2+price model denominator.2+probability.2+
      price model (frame root lengthA lengthB a b numerator.1 denominator.1 result))

theorem value (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data) :
    (run model root lengthA lengthB a b).1=PlayerSpecificAlgebraicPairStep.run model root lengthA lengthB a b := by
  simp only [run,PlayerSpecificFieldCombination.value,PlayerSpecificAlgebraicComparisonExecution.value,
    PlayerSpecificFieldDivisionExecution.value,Bool.false_eq_true,ite_false,ite_true]
  dsimp only [PlayerSpecificAlgebraicPairStep.run]
  split <;> split <;>
    simp_all only [PlayerSpecificFieldCombination.value,ite_true]

end Blotto.PlayerSpecificAlgebraicPairExecution
