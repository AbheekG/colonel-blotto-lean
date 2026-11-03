import Blotto.PlayerSpecificFairSampleCDF
import Blotto.PlayerSpecificZeroUniformCDFContinuity

/-! Downward rounding adds at most d/q0 to the actual marginal CDF
error. The proof handles negative thresholds and zero atoms separately. -/
namespace Blotto.PlayerSpecificDownwardCDFTransport
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem CDF_error {N : ℕ} (R : ℕ) (original rounded : (Fin R → Bool) → Allocation N)
    (target : Mixed N) (ell probability : Fin N → ℝ) (hell : ∀ j,0 < ell j)
    (hp : ∀ j,0 ≤ probability j ∧ probability j ≤ 1)
    (ht : ∀ j,(marginal target j : Measure ℝ)=zeroUniformLaw (ell j) (probability j))
    (q0 d delta : ℝ) (hq : 0 < q0) (hqe : ∀ j,q0 ≤ ell j) (hd : 0 ≤ d)
    (hn : ∀ bits j,0 ≤ rounded bits j) (hdown : ∀ bits j,rounded bits j ≤ original bits j)
    (hgap : ∀ bits j,original bits j-rounded bits j ≤ d)
    (hc : CDFClose ((fairBitLaw R).map original) target delta) :
    CDFClose ((fairBitLaw R).map rounded) target (delta+d/q0) := by
  intro j z
  have hdq : 0 ≤ d/q0 := div_nonneg hd hq.le
  by_cases hz : z < 0
  · have hy := PlayerSpecificFairSampleCDF.negative R rounded j z (fun bits => hn bits j) hz
    have ht0 : closedCDF target j z=0 := by
      unfold closedCDF
      rw [ht j]
      exact PlayerSpecificZeroUniformCDFContinuity.negative_CDF (ell j) (probability j) z (hell j) (hp j) hz
    rw [hy,ht0,sub_self,abs_zero]
    exact add_nonneg ((abs_nonneg _).trans (hc j z)) hdq
  · have hz0 : 0 ≤ z := le_of_not_gt hz
    have hs := PlayerSpecificFairSampleCDF.sandwich R original rounded d hdown hgap j z
    have h0 := abs_le.mp (hc j z)
    have h1 := abs_le.mp (hc j (z+d))
    have hi : closedCDF target j (z+d)-closedCDF target j z ≤ d/q0 := by
      simp only [closedCDF,ht j]
      calc
        _ ≤ d/ell j := PlayerSpecificZeroUniformCDFContinuity.increment (ell j) (probability j) z d (hell j) (hp j) hz0 hd
        _ ≤ d/q0 := div_le_div_of_nonneg_left hd hq (hqe j)
    apply abs_le.mpr
    constructor
    · linarith only [hs.1,h0.1,hdq]
    · linarith only [hs.2,h1.2,hi]

end Blotto.PlayerSpecificDownwardCDFTransport
