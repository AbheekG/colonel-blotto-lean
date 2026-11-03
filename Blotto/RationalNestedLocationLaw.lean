import Blotto.RationalNestedComponents
import Blotto.AveragedBitMixtures

/-! Exact rational descriptor laws averaged over the finite location draw.
This separates the outer location error from all inner component/midpoint
sampling errors, so the remaining branches can use one shared cap. -/

namespace Blotto.RationalNestedInput
open MeasureTheory

noncomputable def firstLocationLaw (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits =>
    (i.firstConditionalLottery htv (i.midpointLocation K bits) (i.midpointLocation_bounds K bits)).real.law)
    (measurable_of_countable _)

theorem firstLocationLaw_eq (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    i.firstLocationLaw htv K = i.real.firstLocationApproximation (i.firstCase_real htv) K := by
  unfold firstLocationLaw
  rw [averaged_fairBit_finite, i.real.firstLocationApproximation_eq_mixture (i.firstCase_real htv) K]
  congr 1
  funext scalarIndex
  rw [i.firstConditionalLottery_law]
  have hs : (i.midpointLocation K ((bitIndexEquiv K).symm scalarIndex) : ℝ) = i.real.location (midpoint scalarIndex) := by
    rw [i.midpointLocation_real, dyadicMidpointSample_real]
    change i.real.location (midpoint ((bitIndexEquiv K) ((bitIndexEquiv K).symm scalarIndex))) = _
    rw [Equiv.apply_symm_apply]
  rw [hs]

theorem firstLocationLaw_CDF_error (i : RationalNestedInput) (htv : i.t ≤ i.v) (K : ℕ) :
    CDFClose (i.firstLocationLaw htv K) (i.real.firstLaw (i.firstCase_real htv)) (1 / (2 : ℝ) ^ K) := by
  rw [i.firstLocationLaw_eq]
  exact i.real.firstLocationApproximation_CDF_error (i.firstCase_real htv) K

noncomputable def familyLocationLaw (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.familyLottery x hx0 hxv K bits).real.law) (measurable_of_countable _)

theorem familyLocationLaw_eq (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) :
    i.familyLocationLaw x hx0 hxv K = (i.familyInput x hx0 hxv).firstLocationLaw hxv K := rfl

theorem familyLocationLaw_CDF_error (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) (K : ℕ) :
    CDFClose (i.familyLocationLaw x hx0 hxv K)
      (i.real.familyFirstLaw x (by exact_mod_cast hx0)
        (by rw [← i.v_real]; exact_mod_cast hxv)) (1 / (2 : ℝ) ^ K) := by
  rw [i.familyLocationLaw_eq]
  have h := (i.familyInput x hx0 hxv).firstLocationLaw_CDF_error hxv K
  simpa only [i.familyInput_real x hx0 hxv, NestedInput.familyFirstLaw] using h

end Blotto.RationalNestedInput
