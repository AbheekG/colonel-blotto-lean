import Blotto.PlayerSpecificSignControlCost

/-! A uniform original-input envelope for all actual cached sign
preparation coefficients, measured widths and integer control prices. -/
namespace Blotto.PlayerSpecificSignPreparationBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 3000000

def coefficient : ℕ := 1024*(PlayerSpecificPreparationBudget.linearCoefficient+
  PlayerSpecificAlgebraicInverseContract.widthCoefficient+PlayerSpecificSquarefreeHeights.certificateConstant+
  PlayerSpecificSquarefreeHeights.quotientConstant+PlayerSpecificExtendedGCDHeights.linearConstant+1000)
def height (H : ℕ) : ℕ := coefficient*(H+1)
def width (H : ℕ) : ℕ := 100000*(height H+1)

theorem large (H : ℕ) : H+1≤height H := by
  have h : 1≤coefficient := by unfold coefficient; omega
  simpa only [height,one_mul] using Nat.mul_le_mul_right (H+1) h

theorem dominated (c H : ℕ) (hc : c≤coefficient) : c*(H+1)≤height H := Nat.mul_le_mul_right _ hc

theorem original_heights (m a : Data) (node : Interval) :
    let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
    HasHeight m H ∧ HasHeight a H ∧ HasHeight [node.lo,node.hi] H ∧ 1≤H := by
  have hi:=PlayerSpecificSignLinearSizes.input_heights m a node
  refine ⟨hi.1,hi.2.1,?_,hi.2.2.2.2⟩
  exact mono (input_height [node.lo,node.hi]) hi.2.2.2.1

theorem unit_height (H : ℕ) : PlayerSpecificAlgebraicUnitExecution.outputHeight H≤height H := by
  unfold PlayerSpecificAlgebraicUnitExecution.outputHeight PlayerSpecificAlgebraicUnitExecution.certificateHeight
  have hh:=dominated (2*PlayerSpecificExtendedGCDHeights.linearConstant) H (by unfold coefficient; omega)
  simpa only [mul_assoc] using hh

theorem control_size (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    PlayerSpecificSignControlBudget.size (PlayerSpecificSignEnclosure.endpointHeight node)
      (PlayerSpecificRationalMagnitude.inputHeight a)
      (PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a))≤
        height (PlayerSpecificSignLinearSizes.inputHeight m a node) := by
  let H:=PlayerSpecificSignLinearSizes.inputHeight m a node
  have hi:=PlayerSpecificSignLinearSizes.input_heights m a node
  have hb:=PlayerSpecificSignLinearSizes.certificate_bounds m a node hml hal
  have hs : PlayerSpecificSignControlBudget.size (PlayerSpecificSignEnclosure.endpointHeight node)
      (PlayerSpecificRationalMagnitude.inputHeight a)
      (PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a))≤
        (68*PlayerSpecificExtendedGCDHeights.linearConstant+120)*(H+1) := by
    unfold PlayerSpecificSignControlBudget.size
    nlinarith only [hi.2.2.1,hi.2.2.2.1,hb.2]
  exact hs.trans (dominated _ H (by unfold coefficient; omega))

theorem control_width (E A B H : ℕ) (hs : PlayerSpecificSignControlBudget.size E A B≤height H) :
    PlayerSpecificSignControlCost.width E A B≤width H := by
  unfold PlayerSpecificSignControlCost.width PlayerSpecificSignControlBudget.word width
  omega

theorem measurement_width (H G : ℕ) (hG : G≤height H) : PlayerSpecificInputWidthExecution.width G≤width H := by
  unfold PlayerSpecificInputWidthExecution.width width
  omega

theorem polynomial_width (H : ℕ) : PlayerSpecificPreparationBudget.width H≤width H := by
  have hp:=PlayerSpecificPreparationBudget.width_linear H
  have hm:=dominated PlayerSpecificPreparationBudget.linearCoefficient H (by unfold coefficient; omega)
  exact hp.trans (hm.trans (by unfold width; omega))

theorem unit_width (H : ℕ) : PlayerSpecificAlgebraicUnitExecution.width H≤width H := by
  have hm : PlayerSpecificAlgebraicUnitExecution.width H≤PlayerSpecificAlgebraicInverseExecution.width H := by
    unfold PlayerSpecificAlgebraicInverseExecution.width
    omega
  have hi:=PlayerSpecificAlgebraicInverseContract.width_linear H
  have hd:=dominated PlayerSpecificAlgebraicInverseContract.widthCoefficient H (by unfold coefficient; omega)
  exact hm.trans (hi.trans (hd.trans (by unfold width; omega)))

theorem copy_width (H : ℕ) : 1+2*height H≤width H ∧ 32≤width H := by unfold width; omega

theorem polynomial_heights (m : Data) (H : ℕ) (hm : HasHeight m H) (hH : 1≤H) (hml : m.length≤4) :
    HasHeight (PlayerSpecificPolynomialPreparation.run m).1.polynomial (height H) ∧
      HasHeight (PlayerSpecificPolynomialPreparation.run m).1.unitRight (height H) ∧
      (PlayerSpecificPolynomialPreparation.run m).1.polynomial.length≤4 ∧
      (PlayerSpecificPolynomialPreparation.run m).1.unitRight.length≤17 ∧
      (PlayerSpecificPolynomialPreparation.run m).1.rows.length≤5 ∧
      (∀ row∈(PlayerSpecificPolynomialPreparation.run m).1.rows,HasHeight row (height H) ∧ row.length≤4) := by
  have hv:=PlayerSpecificPolynomialPreparation.values m
  have hq:=PlayerSpecificSquarefreeHeights.quotient_bounds m H hm hH hml
  have hu:=PlayerSpecificSquarefreeHeights.unitRight_bounds m H hm hH hml
  have hrows:=PlayerSpecificSturmHeights.rows_bounds m H hm hH hml
  have hrl:=PlayerSpecificSturmHeights.rows_length m H hm hH hml
  have hqh : PlayerSpecificSquarefreeHeights.quotientHeight H≤height H :=
    (PlayerSpecificSquarefreeHeights.quotient_linear H).trans
      (dominated PlayerSpecificSquarefreeHeights.quotientConstant H (by unfold coefficient; omega))
  have huh : 2*PlayerSpecificSquarefreeHeights.certificateHeight H≤height H := by
    have h:=Nat.mul_le_mul_left 2 (PlayerSpecificSquarefreeHeights.certificate_linear H)
    have hd:=dominated (2*PlayerSpecificSquarefreeHeights.certificateConstant) H (by unfold coefficient; omega)
    nlinarith only [h,hd]
  have hrh : PlayerSpecificSquarefreeHeights.certificateHeight H≤height H := by omega
  rw [hv.1,hv.2.1,hv.2.2]
  exact ⟨mono hq.1 hqh,mono hu.1 huh,hq.2,hu.2,hrl,fun row hrow =>
    ⟨mono (hrows row hrow).1 hrh,(hrows row hrow).2⟩⟩

end Blotto.PlayerSpecificSignPreparationBudget
