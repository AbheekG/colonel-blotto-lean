import Blotto.PlayerSpecificBalancedPayloadCost

/-! The actual midpoint materializes its bit buffer once, decodes it
once, shifts the denominator and assembles the rational with traced
arithmetic. Casts and enclosing source/counter copies are explicit. -/
namespace Blotto.PlayerSpecificMidpointExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def buffer (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) : Array Bool×ℕ :=
  (Array.ofFn bits,2*K+price model (PlayerSpecificAlgebraicCallerFrame.run [] (K::List.range K)))

def integer (model : RationalCostModel) (n : ℕ) : ℚ×ℕ :=
  ((n:ℚ),price model (PlayerSpecificAlgebraicCallerFrame.run [[(n:ℚ)]] [n,1]))

def frame (model : RationalCostModel) (K index denominator : ℕ) (result : ℚ) : ℕ :=
  price model (PlayerSpecificAlgebraicCallerFrame.run [[result]] [K,index,denominator,1])

def run (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) : ℚ×ℕ :=
  let data:=buffer model K bits
  let index:=PlayerSpecificBalancedPayloadExecution.run model data.1 0 K
  let exponent:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) K 1
  let denominator:=PlayerSpecificNaturalExecution.binary model Nat.shiftLeft 1 exponent.1
  let indexQ:=integer model index.1
  let denominatorQ:=integer model denominator.1
  let doubled:=scalar .multiply indexQ.1 2
  let numerator:=scalar .add doubled.1 1
  let result:=scalar .divide numerator.1 denominatorQ.1
  (result.1,data.2+index.2+exponent.2+denominator.2+indexQ.2+denominatorQ.2+
    price model doubled.2+price model numerator.2+price model result.2+
      frame model K index.1 denominator.1 result.1)

theorem value (model : RationalCostModel) (K : ℕ) (bits : Fin K → Bool) :
    (run model K bits).1=dyadicMidpointSample K bits := by
  simp only [run,buffer,PlayerSpecificBalancedPayloadExecution.value,PlayerSpecificNaturalExecution.binary_value,
    integer,scalar,Arithmetic.apply,dyadicMidpointSample,balancedBitIndex]
  rfl

end Blotto.PlayerSpecificMidpointExecution
