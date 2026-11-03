import Blotto.PlayerSpecificAlgebraicUnitExecution

/-! Executing exact inversion with an actual cached unit certificate and
bounded modular reduction of its at-most-seventeen coefficients. -/
namespace Blotto.PlayerSpecificAlgebraicInverseExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 3000000

def height (H : ℕ) : ℕ := PlayerSpecificModularHeights.height 17 (PlayerSpecificAlgebraicUnitExecution.outputHeight H)
def width (H : ℕ) : ℕ := PlayerSpecificAlgebraicUnitExecution.width H+
  PlayerSpecificModularBudget.width 17 (PlayerSpecificAlgebraicUnitExecution.outputHeight H)+1024*(height H+H+1)+1024
def frame (m a result : Data) : Trace := copyRow m++copyRow a++copyRow result++[.control a.length]

def run (model : RationalCostModel) (m a : Data) : Data×ℕ :=
  if a=[] then ([],price model (frame m a [])) else
    let unit:=PlayerSpecificAlgebraicUnitExecution.run model m a
    let reduced:=PlayerSpecificModularExecution.run model m [1] unit.1
    (reduced.1,unit.2+reduced.2+price model (frame m a reduced.1))

theorem value (model : RationalCostModel) (m a : Data) : (run model m a).1=PlayerSpecificAlgebraicField.inverse m a := by
  rw [run,PlayerSpecificAlgebraicField.inverse]
  split
  · rfl
  · simp only [PlayerSpecificModularExecution.value,PlayerSpecificAlgebraicUnitExecution.value,
      PlayerSpecificModularHorner.reduceLong]

theorem height_ge (H : ℕ) : H+1≤height H := by
  have hu:=PlayerSpecificAlgebraicUnitExecution.height_ge H
  have hm:=PlayerSpecificModularHeights.height_ge 17 (PlayerSpecificAlgebraicUnitExecution.outputHeight H)
  unfold height PlayerSpecificAlgebraicUnitExecution.outputHeight at hm ⊢
  omega

theorem bounds (model : RationalCostModel) (m a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (ha : Reduced m a) (H : ℕ) (hmH : HasHeight m H) (haH : HasHeight a H) (hH : 1≤H) :
    HasHeight (run model m a).1 (height H) ∧ (run model m a).1.length≤3 := by
  have hal : a.length≤4 := by have hh:=ha.2; omega
  have hu:=PlayerSpecificAlgebraicUnitExecution.bounds model m a H hmH haH hH hml hal
  have huheight:=PlayerSpecificAlgebraicUnitExecution.height_ge H
  have hg : H≤PlayerSpecificAlgebraicUnitExecution.outputHeight H := by
    unfold PlayerSpecificAlgebraicUnitExecution.outputHeight
    omega
  rw [run]
  split
  · exact ⟨nil_height _,by simp⟩
  · have hr:=PlayerSpecificModularHeights.run_height m [1] (PlayerSpecificAlgebraicUnitExecution.run model m a).1
      hm hm0 hml (by simp) (PlayerSpecificAlgebraicUnitExecution.outputHeight H) (mono hmH hg)
      (cons_height (one_height.mono (by omega)) (nil_height _)) hu.1
    have hmheight:=PlayerSpecificModularHeights.fuel_mono (PlayerSpecificAlgebraicUnitExecution.outputHeight H) hu.2
    have hred:=(PlayerSpecificModularHorner.reduced m [1] (PlayerSpecificAlgebraicUnitExecution.run model m a).1 hm hm0).2
    simp only [PlayerSpecificModularExecution.value]
    exact ⟨mono hr hmheight,by omega⟩

theorem frame_cost (model : RationalCostModel) (m a result : Data) (H : ℕ)
    (hm : HasHeight m (height H)) (ha : HasHeight a (height H)) (hr : HasHeight result (height H))
    (hml : m.length≤4) (hal : a.length≤4) (hrl : result.length≤3) :
    price model (frame m a result)≤210*model.rat (width H) := by
  have hw : 32≤width H := by unfold width; omega
  have hHW : 1+2*height H≤width H := by unfold width; omega
  have hmp:=PlayerSpecificExtendedCopyCost.row_cost model m (height H) (width H) hm (by omega) hHW hw
  have hap:=PlayerSpecificExtendedCopyCost.row_cost model a (height H) (width H) ha (by omega) hHW hw
  have hrp:=PlayerSpecificExtendedCopyCost.row_cost model result (height H) (width H) hr (by omega) hHW hw
  have hc:=event_price model (width H) (by omega) (.control a.length) ((control_width _).trans (by omega))
  change price model [.control a.length]≤3*model.rat (width H) at hc
  simp only [frame,price_append]
  nlinarith only [hmp,hap,hrp,hc]

theorem run_cost (model : RationalCostModel) (m a : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (ha : Reduced m a) (H : ℕ) (hmH : HasHeight m H) (haH : HasHeight a H) (hH : 1≤H) :
    (run model m a).2≤7000000000*model.rat (width H) := by
  have hal : a.length≤4 := by have hh:=ha.2; omega
  have hg:=height_ge H
  have hb:=bounds model m a hm hm0 hml ha H hmH haH hH
  have hf:=frame_cost model m a (run model m a).1 H (mono hmH (by omega)) (mono haH (by omega)) hb.1 hml hal hb.2
  cases a with
  | nil =>
    simp only [run,ite_true] at hf ⊢
    exact hf.trans (Nat.mul_le_mul_right _ (by decide : 210≤7000000000))
  | cons q qs =>
    have hu:=PlayerSpecificAlgebraicUnitExecution.bounds model m (q::qs) H hmH haH hH hml hal
    have hc:=PlayerSpecificAlgebraicUnitExecution.run_cost model m (q::qs) H hmH haH hH hml hal
    have hcp:=hc.trans (Nat.mul_le_mul_left 3000000000 (model.monotone
      (show PlayerSpecificAlgebraicUnitExecution.width H≤width H by unfold width; omega)))
    have hbase:=PlayerSpecificAlgebraicUnitExecution.height_ge H
    have hUH : H≤PlayerSpecificAlgebraicUnitExecution.outputHeight H := by
      unfold PlayerSpecificAlgebraicUnitExecution.outputHeight
      omega
    have hr:=PlayerSpecificModularExecutionCost.run_cost model m [1] (PlayerSpecificAlgebraicUnitExecution.run model m (q::qs)).1
      hm hm0 hml (by simp) hu.2 (PlayerSpecificAlgebraicUnitExecution.outputHeight H) (mono hmH hUH)
      (cons_height (one_height.mono (by omega)) (nil_height _)) hu.1
    have hwm : PlayerSpecificModularBudget.width (PlayerSpecificAlgebraicUnitExecution.run model m (q::qs)).1.length
        (PlayerSpecificAlgebraicUnitExecution.outputHeight H)≤
        PlayerSpecificModularBudget.width 17 (PlayerSpecificAlgebraicUnitExecution.outputHeight H) :=
      PlayerSpecificModularBudget.width_mono (PlayerSpecificAlgebraicUnitExecution.outputHeight H) hu.2
    have hwidth : PlayerSpecificModularBudget.width (PlayerSpecificAlgebraicUnitExecution.run model m (q::qs)).1.length
        (PlayerSpecificAlgebraicUnitExecution.outputHeight H)≤width H := hwm.trans (by unfold width; omega)
    have hwork: 200000000*((PlayerSpecificAlgebraicUnitExecution.run model m (q::qs)).1.length+1)≤3600000000 := by omega
    have hrp:=hr.trans (Nat.mul_le_mul hwork (model.monotone hwidth))
    simp only [run,List.cons_ne_nil,ite_false] at hf ⊢
    nlinarith only [hcp,hrp,hf]

end Blotto.PlayerSpecificAlgebraicInverseExecution
