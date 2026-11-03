import Blotto.PlayerSpecificSelectedExecutionCost

/-! Complete source prices for both original endpoint queries and their
actual defining-polynomial variation record. -/
namespace Blotto.PlayerSpecificSignRetagCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificSignPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem query_width (m a : Data) (node : Interval) :
    PlayerSpecificPreparedQueryCost.queryWidth m (height (PlayerSpecificSignLinearSizes.inputHeight m a node))≤
      width (PlayerSpecificSignLinearSizes.inputHeight m a node) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi : PlayerSpecificRationalMagnitude.inputHeight m≤H := by unfold H PlayerSpecificSignLinearSizes.inputHeight; omega
  have hc:=PlayerSpecificSquarefreeHeights.certificate_linear (PlayerSpecificRationalMagnitude.inputHeight m)
  have hm:=Nat.mul_le_mul_left PlayerSpecificSquarefreeHeights.certificateConstant (Nat.add_le_add_right hi 1)
  have hd:=dominated PlayerSpecificSquarefreeHeights.certificateConstant H (by unfold coefficient; omega)
  have hcert : PlayerSpecificSquarefreeHeights.certificateHeight (PlayerSpecificRationalMagnitude.inputHeight m)≤height H := hc.trans (hm.trans hd)
  unfold PlayerSpecificPreparedQueryCost.queryWidth PlayerSpecificPreparedQueryCost.queryHeight width
  change 22*(PlayerSpecificSquarefreeHeights.certificateHeight (PlayerSpecificRationalMagnitude.inputHeight m)+height H+1)+48≤100000*(height H+1)
  omega

theorem run_cost (model : RationalCostModel) (m a : Data) (node : Interval) (prepared : Prepared m)
    (hml : m.length≤4) (hv : node.lo<node.hi) :
    price model (PlayerSpecificSignRetagExecution.run prepared node).2≤
      9000*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=original_heights m a node
  have hlarge:=large H
  have hw:=copy_width H
  have hlo : RationalHeight node.lo (height H) := (hi.2.2.1 node.lo (by simp)).mono (by omega)
  have hhi : RationalHeight node.hi (height H) := (hi.2.2.1 node.hi (by simp)).mono (by omega)
  have hl:=PlayerSpecificPreparedQueryCost.endpoint_cost model m prepared hml node.lo (height H) hlo
  have hh:=PlayerSpecificPreparedQueryCost.endpoint_cost model m prepared hml node.hi (height H) hhi
  have hlp:=hl.trans (Nat.mul_le_mul_left 4000 (model.monotone (query_width m a node)))
  have hhp:=hh.trans (Nat.mul_le_mul_left 4000 (model.monotone (query_width m a node)))
  have hvnew:=PlayerSpecificSignEnclosure.initial_valid prepared node hv
  have hcounts:=PlayerSpecificSplitExecution.stored_counts m prepared hml (PlayerSpecificSignEnclosure.retag prepared node) hvnew
  have hr:=PlayerSpecificSplitTraceCost.copyInterval_cost model (PlayerSpecificSignEnclosure.retag prepared node) (height H) (width H)
    hlo hhi hcounts.1 hcounts.2.1 hw.1 (by omega)
  have hin:=PlayerSpecificExtendedCopyCost.row_cost model [node.lo,node.hi] (height H) (width H)
    (mono hi.2.2.1 (by omega)) (by simp) hw.1 hw.2
  have hc:=event_price model (width H) (by omega) (.control 2) ((PlayerSpecificRationalTrace.control_width 2).trans (by omega))
  change price model [.control 2]≤3*model.rat (width H) at hc
  rw [PlayerSpecificSignRetagExecution.run]
  dsimp only
  simp only [price_append]
  simp only [PlayerSpecificSignEnclosure.retag,initial,←PlayerSpecificEndpointExecution.endpoint_value] at hr
  nlinarith only [hlp,hhp,hr,hin,hc]

end Blotto.PlayerSpecificSignRetagCost
