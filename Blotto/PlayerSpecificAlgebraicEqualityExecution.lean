import Blotto.PlayerSpecificAlgebraicExpressionFixedCost

/-! Measured exact field equality. Reduced subtraction is executed once,
then its cached row is tested for zero. Input/result/caller copies are priced. -/
namespace Blotto.PlayerSpecificAlgebraicEqualityExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (m a b difference : Data) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [m,a,b,difference] [1,3]

def run (model : RationalCostModel) (m a b : Data) : Bool×ℕ :=
  let difference:=PlayerSpecificFieldCombination.run true m a b
  let zero:=PlayerSpecificAlgebraicZeroExecution.run model difference.1
  (zero.1,price model difference.2+zero.2+price model (frame m a b difference.1))

theorem value (model : RationalCostModel) (m a b : Data) :
    (run model m a b).1=PlayerSpecificAlgebraicField.equal m a b := by
  simp only [run,PlayerSpecificAlgebraicZeroExecution.run,PlayerSpecificFieldCombination.value,
    ite_true,PlayerSpecificAlgebraicField.equal]

end Blotto.PlayerSpecificAlgebraicEqualityExecution
