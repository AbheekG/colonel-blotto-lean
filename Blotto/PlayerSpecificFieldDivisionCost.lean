import Blotto.PlayerSpecificFieldDivisionExecution

/-! Complete source price for the actual inverse/multiply division caller,
including every retained m/a/b row and the returned reduced coefficients. -/
namespace Blotto.PlayerSpecificFieldDivisionCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificFieldDivisionExecution
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem height_ge (H : ℕ) : H+1≤height H := by
  have hh:=PlayerSpecificModularHeights.height_ge 3 (coefficientHeight H)
  unfold height coefficientHeight at hh ⊢
  omega

theorem copy_width (H : ℕ) : 1+2*height H≤width H ∧ 32≤width H := by
  unfold width
  omega

theorem frame_cost (model : RationalCostModel) (m a b result : Data) (H : ℕ)
    (hmH : HasHeight m (height H)) (haH : HasHeight a (height H))
    (hbH : HasHeight b (height H)) (hrH : HasHeight result (height H))
    (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3) (hrl : result.length≤3) :
    price model (frame m a b result)≤300*model.rat (width H) := by
  have hw:=copy_width H
  have hmp:=PlayerSpecificExtendedCopyCost.row_cost model m _ (width H) hmH (by omega) hw.1 hw.2
  have hap:=PlayerSpecificExtendedCopyCost.row_cost model a _ (width H) haH (by omega) hw.1 hw.2
  have hbp:=PlayerSpecificExtendedCopyCost.row_cost model b _ (width H) hbH (by omega) hw.1 hw.2
  have hrp:=PlayerSpecificExtendedCopyCost.row_cost model result _ (width H) hrH (by omega) hw.1 hw.2
  have hctrl:=event_price model (width H) (by omega) (.control 1) ((control_width 1).trans (by omega))
  change price model [.control 1]≤3*model.rat (width H) at hctrl
  simp only [frame,price_append]
  nlinarith only [hmp,hap,hbp,hrp,hctrl]

theorem run_cost (model : RationalCostModel) (m a b : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b) (H : ℕ)
    (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    (run model m a b).2≤8000000000*model.rat (width H) := by
  have hal : a.length≤3 := by have hl:=ha.2; omega
  have hbl : b.length≤3 := by have hl:=hb.2; omega
  have hi:=PlayerSpecificAlgebraicInverseExecution.bounds model m b hm hm0 hml hb H hmH hbH hH
  have hic:=PlayerSpecificAlgebraicInverseExecution.run_cost model m b hm hm0 hml hb H hmH hbH hH
  have hicp:=hic.trans (Nat.mul_le_mul_left 7000000000 (model.monotone
    (show PlayerSpecificAlgebraicInverseExecution.width H≤width H by unfold width; omega)))
  have hU : H≤coefficientHeight H := by unfold coefficientHeight; omega
  have hI : PlayerSpecificAlgebraicInverseExecution.height H≤coefficientHeight H := by unfold coefficientHeight; omega
  have hc:=PlayerSpecificModularExecutionCost.run_cost model m (PlayerSpecificAlgebraicInverseExecution.run model m b).1 a
    hm hm0 hml hi.2 (by omega) (coefficientHeight H) (mono hmH hU) (mono hi.1 hI) (mono haH hU)
  have hmword : PlayerSpecificModularBudget.width a.length (coefficientHeight H)≤
      PlayerSpecificModularBudget.width 3 (coefficientHeight H) := PlayerSpecificModularBudget.width_mono _ hal
  have hword : PlayerSpecificModularBudget.width a.length (coefficientHeight H)≤width H :=
    hmword.trans (by unfold width; omega)
  have hsteps : 200000000*(a.length+1)≤800000000 := by omega
  have hcp:=hc.trans (Nat.mul_le_mul hsteps (model.monotone hword))
  have hg:=height_ge H
  have hout:=bounds model m a b hm hm0 hml ha hb H hmH haH hbH hH
  have hf:=frame_cost model m a b (run model m a b).1 H (mono hmH (by omega)) (mono haH (by omega))
    (mono hbH (by omega)) hout.2.2 hml hal hbl hout.2.1
  simp only [run] at hf ⊢
  nlinarith only [hicp,hcp,hf]

end Blotto.PlayerSpecificFieldDivisionCost
