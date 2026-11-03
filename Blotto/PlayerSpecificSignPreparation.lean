import Blotto.PlayerSpecificSignControlExecution

/-! Cached actual sign preparation. The field-unit coefficient and the
squarefree/Sturm polynomial cache are distinct, computed once each, and
all width/precision data come from actual stored rows/endpoints. -/
namespace Blotto.PlayerSpecificSignPreparation
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Result where
  polynomials : PlayerSpecificPolynomialPreparation.Result
  unit : Data
  controls : PlayerSpecificSignControlExecution.Result
  endpointHeight : ℕ
  elementHeight : ℕ
  unitHeight : ℕ

def copy (r : Result) : ℕ :=
  PlayerSpecificSignControlExecution.copy r.controls+
  64*(([r.endpointHeight,r.elementHeight,r.unitHeight]).map (fun n => 1+binaryWordWidth n)).sum

def run (model : RationalCostModel) (m a : Data) (node : Interval) : Result×ℕ :=
  let polynomials:=PlayerSpecificPolynomialPreparation.run m
  let unit:=PlayerSpecificAlgebraicUnitExecution.run model m a
  let endpoints:=PlayerSpecificInputWidthExecution.run model [node.lo,node.hi]
  let element:=PlayerSpecificInputWidthExecution.run model a
  let unitWidth:=PlayerSpecificInputWidthExecution.run model unit.1
  let controls:=PlayerSpecificSignControlExecution.run model endpoints.1 element.1 unitWidth.1 a.length unit.1.length
  let result:Result:=⟨polynomials.1,unit.1,controls.1,endpoints.1,element.1,unitWidth.1⟩
  (result,price model polynomials.2+unit.2+endpoints.2+element.2+unitWidth.2+controls.2+
    price model (copyRow m)+price model (copyRow a)+price model (copyRow unit.1)+
    price model (copyRow polynomials.1.polynomial)+price model (copyRow polynomials.1.unitRight)+
    price model (PlayerSpecificSturmExecution.copyRows polynomials.1.rows)+
    price model (copyRow [node.lo,node.hi])+copy result)

theorem unit_value (model : RationalCostModel) (m a : Data) (node : Interval) :
    (run model m a node).1.unit=PlayerSpecificAlgebraicBezout.right m a := PlayerSpecificAlgebraicUnitExecution.value model m a

theorem rows_value (model : RationalCostModel) (m a : Data) (node : Interval) :
    (run model m a node).1.polynomials.rows=PlayerSpecificSturmRootCount.rows m := (PlayerSpecificPolynomialPreparation.values m).2.2

theorem measured_values (model : RationalCostModel) (m a : Data) (node : Interval) :
    (run model m a node).1.endpointHeight=PlayerSpecificSignEnclosure.endpointHeight node ∧
      (run model m a node).1.elementHeight=PlayerSpecificRationalMagnitude.inputHeight a ∧
      (run model m a node).1.unitHeight=PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a) := by
  simp only [run,PlayerSpecificInputWidthExecution.value,PlayerSpecificAlgebraicUnitExecution.value,
    PlayerSpecificSignEnclosure.endpointHeight,and_self]

theorem control_values (model : RationalCostModel) (m a : Data) (node : Interval) :
    let r:=(run model m a node).1.controls
    r.magnitude=PlayerSpecificSignEnclosure.magnitude node ∧
      r.lipschitz=PlayerSpecificAlgebraicSignMagnitude.lipschitz a (PlayerSpecificSignEnclosure.magnitude node) ∧
      r.gap=PlayerSpecificAlgebraicSignMagnitude.gapDenominator m a (PlayerSpecificSignEnclosure.magnitude node) ∧
      r.depth=PlayerSpecificSignPrecision.depth m a node := by
  have h:=PlayerSpecificSignControlExecution.values model (PlayerSpecificSignEnclosure.endpointHeight node)
    (PlayerSpecificRationalMagnitude.inputHeight a) (PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a))
    a.length (PlayerSpecificAlgebraicBezout.right m a).length
  simp only [run,PlayerSpecificInputWidthExecution.value,PlayerSpecificAlgebraicUnitExecution.value]
  exact ⟨h.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩

end Blotto.PlayerSpecificSignPreparation
