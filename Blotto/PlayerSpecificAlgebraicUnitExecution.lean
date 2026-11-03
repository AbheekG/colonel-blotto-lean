import Blotto.PlayerSpecificModularExecutionCost

/-! Cached executing right unit certificate. One actual extended Euclidean
return feeds the head inverse and scaling, with all retained copies priced. -/
namespace Blotto.PlayerSpecificAlgebraicUnitExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 3000000

def certificateHeight (H : ℕ) : ℕ := PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)
def outputHeight (H : ℕ) : ℕ := 2*certificateHeight H
def width (H : ℕ) : ℕ := PlayerSpecificGCDTraceCost.capWidth H+1024*(certificateHeight H+1)+1024

def run (model : RationalCostModel) (m a : Data) : Data×ℕ :=
  let certificate:=PlayerSpecificExtendedGCDExecution.run m a
  let inverted:=PlayerSpecificHeadInverseExecution.run certificate.1.gcd
  let scaled:=PlayerSpecificDenseExecution.scale inverted.1 certificate.1.right
  (scaled.1,price model certificate.2+price model inverted.2+price model scaled.2+
    price model (copyRow m)+price model (copyRow a)+price model (copyRow scaled.1)+price model [.control 1])

theorem value (model : RationalCostModel) (m a : Data) : (run model m a).1=PlayerSpecificAlgebraicBezout.right m a := by
  simp only [run,PlayerSpecificDenseExecution.scale_value,PlayerSpecificHeadInverseExecution.value,
    PlayerSpecificExtendedGCDExecution.value,PlayerSpecificAlgebraicBezout.right,PlayerSpecificAlgebraicBezout.certificate]

theorem height_ge (H : ℕ) : H+1≤certificateHeight H := by
  have hp:=Nat.mul_le_mul_right (H+1) PlayerSpecificEuclideanBudget.constant_pos
  simpa only [certificateHeight,one_mul] using hp

theorem bounds (model : RationalCostModel) (m a : Data) (H : ℕ) (hm : HasHeight m H) (ha : HasHeight a H)
    (hH : 1≤H) (hml : m.length≤4) (hal : a.length≤4) :
    HasHeight (run model m a).1 (outputHeight H) ∧ (run model m a).1.length≤17 := by
  have hc:=PlayerSpecificExtendedGCDExecution.run_bounds m a H hm ha hH hml hal
  have hi:=PlayerSpecificHeadInverseExecution.height _ (certificateHeight H) hc.1 (by have hh:=height_ge H; omega)
  have hs:=scale_height hi hc.2.2.1
  constructor
  · change HasHeight (PlayerSpecificDenseExecution.scale
      (PlayerSpecificHeadInverseExecution.run (PlayerSpecificExtendedGCDExecution.run m a).1.gcd).1
      (PlayerSpecificExtendedGCDExecution.run m a).1.right).1 (outputHeight H)
    rw [PlayerSpecificDenseExecution.scale_value]
    simpa only [outputHeight,certificateHeight,two_mul] using hs
  · change (PlayerSpecificDenseExecution.scale
      (PlayerSpecificHeadInverseExecution.run (PlayerSpecificExtendedGCDExecution.run m a).1.gcd).1
      (PlayerSpecificExtendedGCDExecution.run m a).1.right).1.length≤17
    rw [PlayerSpecificDenseExecution.scale_value,scale_length]
    exact hc.2.2.2.2.2

theorem run_cost (model : RationalCostModel) (m a : Data) (H : ℕ) (hm : HasHeight m H) (ha : HasHeight a H)
    (hH : 1≤H) (hml : m.length≤4) (hal : a.length≤4) :
    (run model m a).2≤3000000000*model.rat (width H) := by
  have hh:=height_ge H
  have hc:=PlayerSpecificExtendedGCDExecution.run_bounds m a H hm ha hH hml hal
  have hs:=bounds model m a H hm ha hH hml hal
  have heg:=PlayerSpecificExtendedGCDTraceCost.run_cost model m a H hm ha hH hml hal
  have heg':=heg.trans (Nat.mul_le_mul_left 2000000000 (model.monotone
    (show PlayerSpecificGCDTraceCost.capWidth H≤width H by unfold width; omega)))
  have hhead:=PlayerSpecificHeadInverseExecution.run_cost model _ (certificateHeight H) 4 hc.1 (by omega) hc.2.2.2.1
  have hhead':=hhead.trans (Nat.mul_le_mul_left _ (model.monotone
    (show PlayerSpecificHeadInverseExecution.width (certificateHeight H) 4≤width H by
      unfold PlayerSpecificHeadInverseExecution.width width; omega)))
  have hinv:=PlayerSpecificHeadInverseExecution.height _ (certificateHeight H) hc.1 (by omega)
  have hscale:=PlayerSpecificDenseOperationCost.scale_cost model _ _ (certificateHeight H) 17 hinv hc.2.2.1 hc.2.2.2.2.2
  have hsw : PlayerSpecificCompositeTraceFits.width (certificateHeight H) 17≤width H := by
    unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height width
    omega
  unfold PlayerSpecificDenseOperationCost.cost at hscale
  have hscale':=hscale.trans (Nat.mul_le_mul_left _ (model.monotone hsw))
  norm_num only [PlayerSpecificDenseOperationCost.traceCap,Nat.reduceAdd,Nat.reducePow,Nat.reduceMul] at hscale'
  have hW : 32≤width H := by unfold width; omega
  have hCW : 1+2*outputHeight H≤width H := by unfold width outputHeight; omega
  have hmp:=PlayerSpecificExtendedCopyCost.row_cost model m (outputHeight H) (width H)
    (mono hm (by unfold outputHeight; omega)) (by omega) hCW hW
  have hap:=PlayerSpecificExtendedCopyCost.row_cost model a (outputHeight H) (width H)
    (mono ha (by unfold outputHeight; omega)) (by omega) hCW hW
  have hresult:=PlayerSpecificExtendedCopyCost.row_cost model (run model m a).1 (outputHeight H) (width H)
    hs.1 (by omega) hCW hW
  have hctrl:=event_price model (width H) (by omega) (.control 1) ((control_width 1).trans (by omega))
  change price model [.control 1]≤3*model.rat (width H) at hctrl
  rw [run]
  dsimp only [run] at hresult
  dsimp only
  nlinarith only [heg',hhead',hscale',hmp,hap,hresult,hctrl]

end Blotto.PlayerSpecificAlgebraicUnitExecution
