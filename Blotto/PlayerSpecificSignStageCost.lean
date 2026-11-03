import Blotto.PlayerSpecificSignStages

/-! Opaque component prices keep the full sign-cost proof independent of
large cached-source expansions while retaining their exact actual returns. -/
namespace Blotto.PlayerSpecificSignStageCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificSignPreparationBudget PlayerSpecificSignStages
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem zero_price (model : RationalCostModel) (m a : Data) (node : Interval) (hal : a.length≤3) :
    (PlayerSpecificAlgebraicZeroExecution.run model a).2≤100*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hc:=PlayerSpecificAlgebraicZeroExecution.source_cost model a hal
  have hi:=(PlayerSpecificSignLinearSizes.input_heights m a node).2.2.1
  have hj:=large H
  have hw : 2*PlayerSpecificRationalMagnitude.inputHeight a+32≤width H := by unfold width; omega
  exact hc.trans (Nat.mul_le_mul_left 100 (model.monotone hw))

theorem initial_price (model : RationalCostModel) (m a : Data) (node : Interval) (hml : m.length≤4)
    (hv : node.lo<node.hi) :
    price model (initial model m a node).2≤9000*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) :=
  PlayerSpecificSignRetagCost.run_cost model m a node (prepared model m a node) hml hv

theorem selected_price (model : RationalCostModel) (m a : Data) (node : Interval)
    (hml : m.length≤4) (hal : a.length≤3) (hv : node.lo<node.hi) :
    (selected model m a node).2≤6000*(height (PlayerSpecificSignLinearSizes.inputHeight m a node)+1)*
      model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hinitial:=PlayerSpecificSignEnclosure.initial_valid (prepare m) node hv
  have he:=PlayerSpecificSignEnclosure.endpoints node
  have hb : PlayerSpecificDyadicEndpoints.Bounded (PlayerSpecificSignEnclosure.retag (prepare m) node)
      (PlayerSpecificSignEnclosure.magnitude node:ℚ) := by
    constructor
    · have hh:=(abs_lt.mp he.1).1.le
      exact_mod_cast hh
    · have hh:=(abs_lt.mp he.2).2.le
      exact_mod_cast hh
  have hg : PlayerSpecificRefinementLattice.Grid (PlayerSpecificSignEnclosure.retag (prepare m) node)
      (PlayerSpecificRefinementLattice.denominator node*2^0) := by
    simpa only [PlayerSpecificRefinementLattice.Grid,PlayerSpecificSignEnclosure.retag,PlayerSpecificIsolationState.initial,pow_zero,mul_one]
      using PlayerSpecificRefinementLattice.initial_grid node
  have hc:=PlayerSpecificSelectedExecutionCost.run_cost model m a node (prepare m) hml hal
    (PlayerSpecificSignPrecision.depth m a node) (PlayerSpecificSignEnclosure.retag (prepare m) node) 0
    (by omega) hinitial hg hb
  have hcap:=PlayerSpecificSelectedSizeBudget.endpoint_cap m a node hml hal
    (PlayerSpecificSignPrecision.depth m a node) (le_refl _)
  change 3*PlayerSpecificSignEnclosure.endpointHeight node+PlayerSpecificSignPrecision.depth m a node+2≤height H at hcap
  have hm:=Nat.mul_le_mul_right (6000*model.rat (width H))
    (show PlayerSpecificSignPrecision.depth m a node+1≤height H+1 by omega)
  rw [selected,prepared_value,depth_value,initial_value]
  nlinarith only [hc,hm]

theorem midpoint_price (model : RationalCostModel) (m a : Data) (node : Interval)
    (hml : m.length≤4) (hal : a.length≤3) (hv : node.lo<node.hi) :
    price model (signed model m a node).2≤1000*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=original_heights m a node
  have hlarge:=large H
  have he:=PlayerSpecificSignLinearSizes.endpoint_linear m a node hml hal hv
  have hcap:=dominated (PlayerSpecificSignLinearSizes.depthCoefficient+5) H
    (by unfold coefficient PlayerSpecificSignLinearSizes.depthCoefficient; omega)
  have hlo:=he.1.mono hcap
  have hhi:=he.2.mono hcap
  rw [signed,selected_value]
  exact PlayerSpecificSignMidpointExecution.run_cost model a _ (height H) (width H)
    (mono hi.2.1 (by omega)) hal hlo hhi (by unfold width; omega)

theorem original_copies (model : RationalCostModel) (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    price model (copyRow m)+price model (copyRow a)+price model (copyRow [node.lo,node.hi])+
      price model [.control 0]≤250*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=original_heights m a node
  have hj:=large H
  have hw:=copy_width H
  have hm:=PlayerSpecificExtendedCopyCost.row_cost model m (height H) (width H) (mono hi.1 (by omega)) (by omega) hw.1 hw.2
  have ha:=PlayerSpecificExtendedCopyCost.row_cost model a (height H) (width H) (mono hi.2.1 (by omega)) (by omega) hw.1 hw.2
  have he:=PlayerSpecificExtendedCopyCost.row_cost model [node.lo,node.hi] (height H) (width H) (mono hi.2.2.1 (by omega)) (by simp) hw.1 hw.2
  have hc:=event_price model (width H) (by omega) (.control 0) ((PlayerSpecificRationalTrace.control_width 0).trans (by omega))
  change price model [.control 0]≤3*model.rat (width H) at hc
  nlinarith only [hm,ha,he,hc]

theorem cached_copies (model : RationalCostModel) (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    price model (copyRow m)+price model (copyRow a)+price model (copyRow (cache model m a node).1.unit)+
      price model (PlayerSpecificSturmExecution.copyRows (cache model m a node).1.polynomials.rows)+
      PlayerSpecificSignPreparation.copy (cache model m a node).1+price model [.control 1]≤
        2000*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=original_heights m a node
  have hj:=large H
  have hw:=copy_width H
  have hm:=PlayerSpecificExtendedCopyCost.row_cost model m (height H) (width H) (mono hi.1 (by omega)) (by omega) hw.1 hw.2
  have ha:=PlayerSpecificExtendedCopyCost.row_cost model a (height H) (width H) (mono hi.2.1 (by omega)) (by omega) hw.1 hw.2
  have hu:=PlayerSpecificAlgebraicUnitExecution.bounds model m a H hi.1 hi.2.1 hi.2.2.2 hml (by omega)
  have hup:=PlayerSpecificExtendedCopyCost.row_cost model (cache model m a node).1.unit (height H) (width H)
    (mono hu.1 (unit_height H)) (by change (PlayerSpecificAlgebraicUnitExecution.run model m a).1.length≤21; omega) hw.1 hw.2
  have hp:=polynomial_heights m H hi.1 hi.2.2.2 hml
  have hrp:=PlayerSpecificSturmCopyCost.copyRows_cost model _ (height H) (width H)
    hp.2.2.2.2.2 hp.2.2.2.2.1 hw.1 hw.2
  have hmeta:=PlayerSpecificSignPreparationCopy.integer_copy model m a node hml hal
  change price model (PlayerSpecificSturmExecution.copyRows (cache model m a node).1.polynomials.rows)≤100*model.rat (width H) at hrp
  change PlayerSpecificSignPreparation.copy (cache model m a node).1≤1024*model.rat (width H) at hmeta
  have hc:=event_price model (width H) (by omega) (.control 1) ((PlayerSpecificRationalTrace.control_width 1).trans (by omega))
  change price model [.control 1]≤3*model.rat (width H) at hc
  nlinarith only [hm,ha,hup,hrp,hmeta,hc]

end Blotto.PlayerSpecificSignStageCost
