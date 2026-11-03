import Blotto.PlayerSpecificSignPreparationCopy

/-! Complete cached sign preparation source price from original encoded
input, including all measured widths, integer controls and returned copies. -/
namespace Blotto.PlayerSpecificSignPreparationCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState PlayerSpecificSignPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem measurement (model : RationalCostModel) (p : Data) (H G : ℕ)
    (hp : HasHeight p G) (hlen : p.length≤17) (hG : G≤height H) :
    (PlayerSpecificInputWidthExecution.run model p).2≤40000*(height H+1)*model.rat (width H) := by
  have hc:=PlayerSpecificInputWidthCost.run_cost model p G hp hlen
  exact hc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 40000 (by omega)) (model.monotone (measurement_width H G hG)))

theorem controls (model : RationalCostModel) (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    (PlayerSpecificSignControlExecution.run model
      (PlayerSpecificInputWidthExecution.run model [node.lo,node.hi]).1
      (PlayerSpecificInputWidthExecution.run model a).1
      (PlayerSpecificInputWidthExecution.run model (PlayerSpecificAlgebraicUnitExecution.run model m a).1).1
      a.length (PlayerSpecificAlgebraicUnitExecution.run model m a).1.length).2≤
        1500000*height (PlayerSpecificSignLinearSizes.inputHeight m a node)*
          model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  simp only [PlayerSpecificInputWidthExecution.value,PlayerSpecificAlgebraicUnitExecution.value]
  have hb:=PlayerSpecificSignLinearSizes.certificate_bounds m a node hml hal
  have hs:=control_size m a node hml hal
  have hc:=PlayerSpecificSignControlCost.run_cost model (PlayerSpecificSignEnclosure.endpointHeight node)
    (PlayerSpecificRationalMagnitude.inputHeight a)
    (PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a)) a.length
    (PlayerSpecificAlgebraicBezout.right m a).length hal hb.1
  exact hc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 1500000 hs) (model.monotone (control_width _ _ _ _ hs)))

theorem run_cost (model : RationalCostModel) (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    (PlayerSpecificSignPreparation.run model m a node).2≤
      20000000000*(height (PlayerSpecificSignLinearSizes.inputHeight m a node)+1)*
        model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=original_heights m a node
  have hlarge:=large H
  have hp:=PlayerSpecificPolynomialPreparation.run_cost model m H hi.1 hi.2.2.2 hml
  have hpp:=hp.trans (Nat.mul_le_mul_left 10000000000 (model.monotone (polynomial_width H)))
  have hu:=PlayerSpecificAlgebraicUnitExecution.run_cost model m a H hi.1 hi.2.1 hi.2.2.2 hml (by omega)
  have hup:=hu.trans (Nat.mul_le_mul_left 3000000000 (model.monotone (unit_width H)))
  have hb:=PlayerSpecificAlgebraicUnitExecution.bounds model m a H hi.1 hi.2.1 hi.2.2.2 hml (by omega)
  have hm1:=measurement model [node.lo,node.hi] H H hi.2.2.1 (by simp) (by omega)
  have hm2:=measurement model a H H hi.2.1 (by omega) (by omega)
  have hm3:=measurement model (PlayerSpecificAlgebraicUnitExecution.run model m a).1 H
    (PlayerSpecificAlgebraicUnitExecution.outputHeight H) hb.1 hb.2 (unit_height H)
  have hc:=controls model m a node hml hal
  have hcopies:=PlayerSpecificSignPreparationCopy.rational_copies model m a node hml hal
  have hmeta:=PlayerSpecificSignPreparationCopy.integer_copy model m a node hml hal
  rw [PlayerSpecificSignPreparation.run]
  dsimp only
  dsimp only [PlayerSpecificSignPreparation.run] at hmeta
  dsimp only at hcopies
  nlinarith only [hpp,hup,hm1,hm2,hm3,hc,hcopies,hmeta]

end Blotto.PlayerSpecificSignPreparationCost
