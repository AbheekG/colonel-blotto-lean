import Blotto.PlayerSpecificSignPreparationBudget

/-! Complete copies of the actual cached polynomial, unit coefficient,
endpoint row and measured integer sign-preparation fields. -/
namespace Blotto.PlayerSpecificSignPreparationCopy
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState PlayerSpecificSignPreparationBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem integer_copy (model : RationalCostModel) (m a : Data) (node : Interval)
    (hml : m.length≤4) (hal : a.length≤3) :
    PlayerSpecificSignPreparation.copy (PlayerSpecificSignPreparation.run model m a node).1≤
      1024*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  let E:=PlayerSpecificSignEnclosure.endpointHeight node
  let A:=PlayerSpecificRationalMagnitude.inputHeight a
  let B:=PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a)
  have hb:=PlayerSpecificSignLinearSizes.certificate_bounds m a node hml hal
  have hs : PlayerSpecificSignControlBudget.size E A B≤height H := control_size m a node hml hal
  have hc:=PlayerSpecificSignControlCost.copies model E A B a.length
    (PlayerSpecificAlgebraicBezout.right m a).length hal hb.1
  have hcw:=control_width E A B H hs
  have hcp : PlayerSpecificSignControlExecution.copy (PlayerSpecificSignControlExecution.run model E A B
      a.length (PlayerSpecificAlgebraicBezout.right m a).length).1≤832*model.rat (width H) :=
    (Nat.le_add_right _ _).trans (hc.trans (Nat.mul_le_mul_left 832 (model.monotone hcw)))
  have hw : 32≤width H := (copy_width H).2
  have hfit : ∀ n∈[E,A,B],1+binaryWordWidth n≤width H := by
    have hE : E≤height H := by unfold PlayerSpecificSignControlBudget.size at hs; omega
    have hA : A≤height H := by unfold PlayerSpecificSignControlBudget.size at hs; omega
    have hB : B≤height H := by unfold PlayerSpecificSignControlBudget.size at hs; omega
    intro n hn
    have hnc:=PlayerSpecificRationalTrace.control_width n
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> unfold width <;> omega
  have hsum:=PlayerSpecificSignControlCost.sum_words [E,A,B] (width H) hfit
  simp only [List.length_cons,List.length_nil] at hsum
  have hword:=model.word_le (width H)
  have hmeasured:=PlayerSpecificSignPreparation.measured_values model m a node
  have hcache : (PlayerSpecificSignPreparation.run model m a node).1.controls=
      (PlayerSpecificSignControlExecution.run model E A B a.length (PlayerSpecificAlgebraicBezout.right m a).length).1 := by
    simp only [PlayerSpecificSignPreparation.run,PlayerSpecificInputWidthExecution.value,
      PlayerSpecificAlgebraicUnitExecution.value,E,A,B,PlayerSpecificSignEnclosure.endpointHeight]
  rw [PlayerSpecificSignPreparation.copy,hcache,hmeasured.1,hmeasured.2.1,hmeasured.2.2]
  change _≤1024*model.rat (width H)
  nlinarith only [hcp,hsum,hword]

theorem rational_copies (model : RationalCostModel) (m a : Data) (node : Interval)
    (hml : m.length≤4) (hal : a.length≤3) :
    let polynomials:=PlayerSpecificPolynomialPreparation.run m
    let unit:=PlayerSpecificAlgebraicUnitExecution.run model m a
    price model (copyRow m)+price model (copyRow a)+price model (copyRow unit.1)+
      price model (copyRow polynomials.1.polynomial)+price model (copyRow polynomials.1.unitRight)+
      price model (PlayerSpecificSturmExecution.copyRows polynomials.1.rows)+price model (copyRow [node.lo,node.hi])≤
        500*model.rat (width (PlayerSpecificSignLinearSizes.inputHeight m a node)) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=original_heights m a node
  have hlarge:=large H
  have hw:=copy_width H
  have hu:=PlayerSpecificAlgebraicUnitExecution.bounds model m a H hi.1 hi.2.1 hi.2.2.2 hml (by omega)
  have hp:=polynomial_heights m H hi.1 hi.2.2.2 hml
  have hmprice:=PlayerSpecificExtendedCopyCost.row_cost model m (height H) (width H)
    (mono hi.1 (by omega)) (by omega) hw.1 hw.2
  have haprice:=PlayerSpecificExtendedCopyCost.row_cost model a (height H) (width H)
    (mono hi.2.1 (by omega)) (by omega) hw.1 hw.2
  have heprice:=PlayerSpecificExtendedCopyCost.row_cost model [node.lo,node.hi] (height H) (width H)
    (mono hi.2.2.1 (by omega)) (by simp) hw.1 hw.2
  have huprice:=PlayerSpecificExtendedCopyCost.row_cost model _ (height H) (width H)
    (mono hu.1 (unit_height H)) (by omega) hw.1 hw.2
  have hpprice:=PlayerSpecificExtendedCopyCost.row_cost model _ (height H) (width H) hp.1 (by omega) hw.1 hw.2
  have hcprice:=PlayerSpecificExtendedCopyCost.row_cost model _ (height H) (width H) hp.2.1 (by omega) hw.1 hw.2
  have hrprice:=PlayerSpecificSturmCopyCost.copyRows_cost model _ (height H) (width H)
    hp.2.2.2.2.2 hp.2.2.2.2.1 hw.1 hw.2
  dsimp only
  nlinarith only [hmprice,haprice,heprice,huprice,hpprice,hcprice,hrprice]

end Blotto.PlayerSpecificSignPreparationCopy
