import Blotto.PlayerSpecificZeroUniformAffineCDF

/-! Positive-side CDF increments exclude the atom at zero. These bounds
are used to transport the actual downward coordinate rounding. -/
namespace Blotto.PlayerSpecificZeroUniformCDFContinuity
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem weighted (ell p z : ℝ) (hell : 0 < ell) (hp : 0 ≤ p ∧ p ≤ 1) :
    (zeroUniformLaw ell p).real (Set.Iic z)=
      (1-p)*(Measure.dirac (0:ℝ)).real (Set.Iic z)+p*(uniformLaw ell).real (Set.Iic z) := by
  let : IsProbabilityMeasure (uniformLaw ell) := (uniformMarginal ell hell).property
  rw [zeroUniformLaw,measureReal_add_apply (by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) (by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    measureReal_ennreal_smul_apply,measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2),ENNReal.toReal_ofReal hp.1]

theorem nonnegative_CDF (ell p z : ℝ) (hell : 0 < ell) (hp : 0 ≤ p ∧ p ≤ 1) (hz : 0 ≤ z) :
    (zeroUniformLaw ell p).real (Set.Iic z)=1-p+p*(min z ell/ell) := by
  have hatom : (Measure.dirac (0:ℝ)).real (Set.Iic z)=1 := by simp [Measure.real,hz]
  have hu := uniform_closedCDF ell hell z
  change (uniformLaw ell).real (Set.Iic z)=_ at hu
  rw [weighted ell p z hell hp,hatom,hu,max_eq_left (le_min hz hell.le),mul_one]

theorem negative_CDF (ell p z : ℝ) (hell : 0 < ell) (hp : 0 ≤ p ∧ p ≤ 1) (hz : z < 0) :
    (zeroUniformLaw ell p).real (Set.Iic z)=0 := by
  have hatom : (Measure.dirac (0:ℝ)).real (Set.Iic z)=0 := by simp [Measure.real,not_le.mpr hz]
  have hu := uniform_closedCDF ell hell z
  change (uniformLaw ell).real (Set.Iic z)=_ at hu
  rw [min_eq_left (hz.trans hell).le,max_eq_right hz.le,zero_div] at hu
  rw [weighted ell p z hell hp,hatom,hu,mul_zero,mul_zero,add_zero]

theorem increment (ell p z d : ℝ) (hell : 0 < ell) (hp : 0 ≤ p ∧ p ≤ 1) (hz : 0 ≤ z) (hd : 0 ≤ d) :
    (zeroUniformLaw ell p).real (Set.Iic (z+d))-(zeroUniformLaw ell p).real (Set.Iic z) ≤ d/ell := by
  have hmin : 0 ≤ min (z+d) ell-min z ell := sub_nonneg.mpr (min_le_min (by linarith only [hd]) le_rfl)
  have hbound : min (z+d) ell-min z ell ≤ d := by
    by_cases hze : z ≤ ell
    · rw [min_eq_left hze]
      have h := min_le_left (z+d) ell
      linarith only [h]
    · have he : ell ≤ z := (lt_of_not_ge hze).le
      rw [min_eq_right he,min_eq_right (show ell ≤ z+d by linarith only [he,hd]),sub_self]
      exact hd
  have hpmin : p*(min (z+d) ell-min z ell) ≤ d :=
    (mul_le_mul_of_nonneg_right hp.2 hmin).trans (by simpa only [one_mul] using hbound)
  calc
    _ = (p*(min (z+d) ell-min z ell))/ell := by
      rw [nonnegative_CDF ell p (z+d) hell hp (by linarith only [hz,hd]),nonnegative_CDF ell p z hell hp hz]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hpmin hell.le

end Blotto.PlayerSpecificZeroUniformCDFContinuity
