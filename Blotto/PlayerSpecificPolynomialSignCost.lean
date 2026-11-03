import Blotto.PlayerSpecificPolynomialSignBudget

/-! Complete raw-polynomial exact sign caller source price, including
actual reduction, exact sign and all enclosing copies and controls. -/
namespace Blotto.PlayerSpecificPolynomialSignCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificIsolationState PlayerSpecificRationalTrace PlayerSpecificPolynomialSignBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

def workCoefficient : ℕ := 300001*PlayerSpecificSignContract.workCoefficient+1000000000
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem copies (model : RationalCostModel) (m p : Data) (node : Interval) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hpl : p.length≤4) :
    price model (copyRow m)+price model (copyRow p)+price model (copyRow (PlayerSpecificDivisionExecution.run p m).1.2)+
      price model (copyRow [node.lo,node.hi])+price model [.control 1]≤300*model.rat (width (inputHeight m p node)) := by
  let H:=inputHeight m p node
  have hi:=original_heights m p node
  have hr:=remainder_bounds m p node hm hm0 hml hpl
  have hw:=copy_width H
  have hmprice:=PlayerSpecificExtendedCopyCost.row_cost model m H (width H) hi.1 (by omega) hw.2.1 hw.2.2
  have hpprice:=PlayerSpecificExtendedCopyCost.row_cost model p H (width H) hi.2.1 (by omega) hw.2.1 hw.2.2
  have heprice:=PlayerSpecificExtendedCopyCost.row_cost model [node.lo,node.hi] H (width H) hi.2.2.1 (by simp) hw.2.1 hw.2.2
  have hrprice:=PlayerSpecificExtendedCopyCost.row_cost model _ (remainderHeight H) (width H) hr.2.2 (by omega) hw.1 hw.2.2
  have hc:=event_price model (width H) (by omega) (.control 1) ((PlayerSpecificRationalTrace.control_width 1).trans (by omega))
  change price model [.control 1]≤3*model.rat (width H) at hc
  nlinarith only [hmprice,hpprice,heprice,hrprice,hc]

theorem run_cost (model : RationalCostModel) (m p : Data) (node : Interval) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hpl : p.length≤4) (hv : node.lo<node.hi) :
    (PlayerSpecificPolynomialSignExecution.run model m p node).2≤
      workCoefficient*(inputHeight m p node+1)*model.rat (width (inputHeight m p node)) := by
  let H:=inputHeight m p node
  have hi:=original_heights m p node
  have hr:=remainder_bounds m p node hm hm0 hml hpl
  have hd:=PlayerSpecificDivisionTraceCost.run_cost model p m H hi.2.1 hi.1 hi.2.2.2 hpl hml
  have hdp:=hd.trans (Nat.mul_le_mul_left 100000000 (model.monotone (division_width H)))
  have hinput:=reduced_input_bound m p node hm hm0 hml hpl
  have hs:=PlayerSpecificSignContract.source_cost model m (PlayerSpecificDivisionExecution.run p m).1.2 node hml hr.2.1 hv
  have hwork:=sign_width_profile PlayerSpecificSignContract.workCoefficient
    (PlayerSpecificSignLinearSizes.inputHeight m (PlayerSpecificDivisionExecution.run p m).1.2 node) H hinput
  have hwidth:=sign_width _ H hinput
  have hsp:=hs.trans (Nat.mul_le_mul hwork (model.monotone hwidth))
  have hc:=copies model m p node hm hm0 hml hpl
  rw [PlayerSpecificPolynomialSignExecution.run]
  dsimp only
  unfold workCoefficient
  nlinarith only [hdp,hsp,hc]

end Blotto.PlayerSpecificPolynomialSignCost
