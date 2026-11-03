import Blotto.PlayerSpecificUniformLeafLawGeometry

/-! For an H-independent hybrid, whole-event approximation and the
already checked actual CDF bounds remove the vanishing H-error exactly.
Only the finite scalar midpoint error remains. -/
namespace Blotto.PlayerSpecificHybridLimit
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem vanish (v A E : ℝ) (h : ∀ H : ℕ,v ≤ A/(2:ℝ)^H+E) : v ≤ E := by
  have hp : Tendsto (fun H : ℕ => (1/(2:ℝ))^H) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ha := (hp.const_mul A).add_const E
  have he : Tendsto (fun H : ℕ => A/(2:ℝ)^H+E) atTop (𝓝 E) := by
    simpa only [div_eq_mul_inv,one_mul,inv_pow,mul_zero,zero_add] using ha
  exact ge_of_tendsto he (Eventually.of_forall h)

theorem event_CDF {N : ℕ} (u l : Mixed N) (E : ℝ) (h : PlayerSpecificEventDistance.Bound u l E) : CDFClose u l E := by
  intro j z
  rw [PlayerSpecificResourceContinuationCDF.cdf_event,PlayerSpecificResourceContinuationCDF.cdf_event]
  exact h _ ((measurable_pi_apply j) measurableSet_Iic)

theorem CDF_error {N : ℕ} (actual : ℕ → Mixed N) (hybrid target : Mixed N) (A C E : ℝ)
    (hevent : ∀ H,PlayerSpecificEventDistance.Bound (actual H) hybrid (C/(2:ℝ)^H))
    (hCDF : ∀ H,CDFClose (actual H) target (A/(2:ℝ)^H+E)) : CDFClose hybrid target E := by
  intro j z
  apply vanish _ (A+C) E
  intro H
  have he := (event_CDF (actual H) hybrid _ (hevent H)).symm j z
  calc
    _ ≤ |closedCDF hybrid j z-closedCDF (actual H) j z|+|closedCDF (actual H) j z-closedCDF target j z| := abs_sub_le _ _ _
    _ ≤ C/(2:ℝ)^H+(A/(2:ℝ)^H+E) := add_le_add he (hCDF H j z)
    _ = (A+C)/(2:ℝ)^H+E := by ring

end Blotto.PlayerSpecificHybridLimit
