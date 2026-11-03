import Blotto.PlayerSpecificSignStageCost

/-! Complete original-input source-price join for the actual cached sign
entry, including its zero branch and every nonzero continuation/copy. -/
namespace Blotto.PlayerSpecificSignExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
open PlayerSpecificSignPreparationBudget PlayerSpecificSignStages
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem combine (J R z p i s q c : ℕ) (hz : z≤100*R) (hp : p≤20000000000*(J+1)*R)
    (hi : i≤9000*R) (hs : s≤6000*(J+1)*R) (hq : q≤1000*R) (hc : c≤2000*R) :
    z+p+i+s+q+c≤21000000000*(J+1)*R := by
  nlinarith only [hz,hp,hi,hs,hq,hc]

theorem run_cost (model : RationalCostModel) (m a : Data) (node : Interval)
    (hml : m.length≤4) (hal : a.length≤3) (hv : node.lo<node.hi) :
    (PlayerSpecificSignExecution.run model m a node).2≤
      21000000000*(height (PlayerSpecificSignLinearSizes.inputHeight m a node)+1)*
        model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hz:=PlayerSpecificSignStageCost.zero_price model m a node hal
  have hp:=PlayerSpecificSignPreparationCost.run_cost model m a node hml hal
  change (cache model m a node).2≤20000000000*(height H+1)*model.rat (width H) at hp
  have hi:=PlayerSpecificSignStageCost.initial_price model m a node hml hv
  have hs:=PlayerSpecificSignStageCost.selected_price model m a node hml hal hv
  have hq:=PlayerSpecificSignStageCost.midpoint_price model m a node hml hal hv
  have hc:=PlayerSpecificSignStageCost.cached_copies model m a node hml hal
  have ho:=PlayerSpecificSignStageCost.original_copies model m a node hml hal
  rw [PlayerSpecificSignExecution.run]
  dsimp only
  split
  · nlinarith only [hz,ho]
  · change (PlayerSpecificAlgebraicZeroExecution.run model a).2+(cache model m a node).2+
      price model (initial model m a node).2+(selected model m a node).2+price model (signed model m a node).2+
      price model (copyRow m)+price model (copyRow a)+price model (copyRow (cache model m a node).1.unit)+
      price model (PlayerSpecificSturmExecution.copyRows (cache model m a node).1.polynomials.rows)+
      PlayerSpecificSignPreparation.copy (cache model m a node).1+price model [.control 1]≤_
    have hcombined:=combine (height H) (model.rat (width H)) _ _ _ _ _ _ hz hp hi hs hq hc
    exact le_trans (le_of_eq (by ring)) hcombined

end Blotto.PlayerSpecificSignExecutionCost
