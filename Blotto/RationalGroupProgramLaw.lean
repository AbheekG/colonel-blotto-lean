import Blotto.RationalGroupPrograms
import Blotto.RationalFourSpecLaw
import Blotto.AveragedBitMaps

/-! Exact ideal midpoint laws of the native grouped controllers. Uniform
and three-variable groups need one scalar block; four-variable groups use two. -/

namespace Blotto
open MeasureTheory

namespace RationalSegmentLottery

theorem averaged_machineIdeal {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ) :
    averagedLaw (fairBitLaw K) (fun bits => (l.machine fallback K bits).rationalIdealLaw l.start)
      (measurable_of_countable _) = l.real.dyadicLaw K := by
  calc
    _ = l.idealMidpointLaw K := averaged_fairBit_congr K _ _ (l.machine_rationalIdealLaw fallback K)
    _ = _ := l.idealMidpointLaw_eq K

end RationalSegmentLottery

namespace RationalUniformGroupSpec

noncomputable def midpointLaw {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) : Mixed m :=
  (i.lottery hm).real.dyadicLaw K

theorem averaged_programIdeal {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    averagedLaw (fairBitLaw K) (fun bits => (i.program hm K bits).idealLaw) (measurable_of_countable _) =
      i.midpointLaw hm K := (i.lottery hm).averaged_machineIdeal 0 K

theorem midpointLaw_CDF_error {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    CDFClose (i.midpointLaw hm K) (i.real.law hm) (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.lottery hm).real.dyadicLaw_CDF_error K
  rw [i.lottery_law hm] at h
  exact h.mono (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))

end RationalUniformGroupSpec

namespace RationalMixedGroupSpec

noncomputable def midpointLaw {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) : Mixed (m + 1) :=
  averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
    (fun scalarBits => (i.program hm K outerBits scalarBits).idealLaw) (measurable_of_countable _)) (measurable_of_countable _)

theorem midpointLaw_three (i : RationalMixedGroupSpec 2) (K : ℕ) :
    i.midpointLaw (Or.inl rfl) K = i.threeInput.real.dyadicLaw K := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun _ => i.threeInput.segmentLottery.real.dyadicLaw K) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      change averagedLaw (fairBitLaw K) (fun bits =>
        (i.threeInput.segmentLottery.machine 0 K bits).rationalIdealLaw i.threeInput.segmentLottery.start)
          (measurable_of_countable _) = i.threeInput.segmentLottery.real.dyadicLaw K
      exact i.threeInput.segmentLottery.averaged_machineIdeal 0 K
    _ = _ := by
      rw [averaged_fairBit_constant, i.threeInput.segmentLottery_real]
      rfl

theorem midpointLaw_four (i : RationalMixedGroupSpec 3) (K : ℕ) :
    i.midpointLaw (Or.inr rfl) K = i.fourInput.midpointLaw K := by
  exact i.fourInput.averaged_fixedIdeal K

theorem midpointLaw_CDF_error {m : ℕ} (i : RationalMixedGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) :
    CDFClose (i.midpointLaw hm K) (i.real.law hm) (3 / (2 * (2 : ℝ) ^ K)) := by
  rcases hm with rfl | rfl
  · rw [i.midpointLaw_three]
    have h := i.threeInput.real.dyadicLaw_CDF_error K
    rw [i.threeInput_real] at h
    exact h.mono (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))
  · rw [i.midpointLaw_four]
    have h := i.fourInput.midpointLaw_CDF_error K
    rw [i.fourInput_real] at h
    exact h

end RationalMixedGroupSpec
end Blotto
