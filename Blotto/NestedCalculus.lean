import Blotto.NestedLocation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Calculus identities for the explicit first-case location distribution.
The final conditional-allocation averaging is a separate measure obligation. -/

namespace Blotto.NestedInput
open MeasureTheory Set
open scoped Interval

noncomputable def locationDensity (i : NestedInput) (s : ℝ) : ℝ :=
  i.h * (i.h + i.t) / (i.t * (i.h + s) ^ 2)

theorem locationDensity_nonnegative (i : NestedInput) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ i.locationDensity s := by
  have hh := i.h_pos
  have ht := i.t_pos
  dsimp [locationDensity]
  positivity

theorem hasDerivAt_locationCDF (i : NestedInput) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt i.locationCDF (i.locationDensity s) s := by
  have ht := i.t_pos
  have hh := i.h_pos
  have hhs : i.h + s ≠ 0 := ne_of_gt (by linarith)
  change HasDerivAt (fun y => y * (i.h + i.t) / (i.t * (i.h + y)))
    (i.h * (i.h + i.t) / (i.t * (i.h + s) ^ 2)) s
  convert ((hasDerivAt_id s).mul_const (i.h + i.t)).div
    (((hasDerivAt_const s i.h).add (hasDerivAt_id s)).const_mul i.t)
    (mul_ne_zero (ne_of_gt ht) hhs) using 1
  · ext y
    rfl
  · dsimp
    field_simp [ne_of_gt ht, hhs]
    ring

/-- The displayed density integrates to the exact location CDF on its support. -/
theorem integral_locationDensity (i : NestedInput) {b : ℝ} (hb : 0 ≤ b) :
    (∫ s in (0 : ℝ)..b, i.locationDensity s) = i.locationCDF b := by
  have hden : ∀ s ∈ Icc 0 b, i.t * (i.h + s) ^ 2 ≠ 0 := by
    intro s hs
    exact mul_ne_zero (ne_of_gt i.t_pos) (pow_ne_zero _ (ne_of_gt (by linarith [i.h_pos, hs.1])))
  have hcont : ContinuousOn i.locationDensity (Icc 0 b) :=
    continuousOn_const.div
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).pow 2)) hden
  have hi : IntervalIntegrable i.locationDensity volume 0 b :=
    ContinuousOn.intervalIntegrable_of_Icc hb hcont
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => i.hasDerivAt_locationCDF (by
      have hsc : s ∈ Icc 0 b := by simpa only [uIcc_of_le hb] using hs
      exact hsc.1)) hi
  simpa [locationCDF] using he

end Blotto.NestedInput
