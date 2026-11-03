import Blotto.PlayerSpecificModularExecution

/-! Source envelopes for bounded modular Horner, calibrated entirely from
coefficient heights and actual coefficient-list lengths. -/
namespace Blotto.PlayerSpecificModularBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificModularHeights
set_option autoImplicit false
set_option maxHeartbeats 3000000

def base : ℕ := 16*1000000^6
def width (fuel H : ℕ) : ℕ := base*(height fuel H+1)

theorem large (fuel H : ℕ) : 1024*(height fuel H+1)≤width fuel H :=
  Nat.mul_le_mul_right _ (by norm_num [base])
theorem width_mono (H : ℕ) : Monotone (fun fuel => width fuel H) := by
  intro i j hij
  exact Nat.mul_le_mul_left base (Nat.add_le_add_right (fuel_mono H hij) 1)

theorem division_width (fuel H : ℕ) : 2*1000000^6*(4*height fuel H+1)≤width (fuel+1) H := by
  have hm:=width_mono H (Nat.le_succ fuel)
  have hc : 2*1000000^6*(4*height fuel H+1)≤width fuel H := by unfold width base; omega
  exact hc.trans hm

theorem frame_cost (model : RationalCostModel) (m b a result : Data) (G W : ℕ)
    (hm : HasHeight m G) (hb : HasHeight b G) (ha : HasHeight a G) (hr : HasHeight result G)
    (hml : m.length≤4) (hbl : b.length≤3) (hal : a.length≤17) (hrl : result.length≤3)
    (hGW : 1+2*G≤W) (hW : 32≤W) : price model (PlayerSpecificModularExecution.frame m b a result)≤300*model.rat W := by
  have hmp:=PlayerSpecificExtendedCopyCost.row_cost model m G W hm (by omega) hGW hW
  have hbp:=PlayerSpecificExtendedCopyCost.row_cost model b G W hb (by omega) hGW hW
  have hap:=PlayerSpecificExtendedCopyCost.row_cost model a G W ha (by omega) hGW hW
  have hrp:=PlayerSpecificExtendedCopyCost.row_cost model result G W hr (by omega) hGW hW
  have hc:=event_price model W (by omega) (.control a.length) ((control_width _).trans (by omega))
  change price model [.control a.length]≤3*model.rat W at hc
  simp only [PlayerSpecificModularExecution.frame,price_append]
  nlinarith only [hmp,hbp,hap,hrp,hc]

end Blotto.PlayerSpecificModularBudget
