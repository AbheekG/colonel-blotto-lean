import Blotto.PlayerSpecificNestedAffineCDF

/-! Zero/uniform marginal CDFs are affine in the native resource row.
The atom at zero is retained exactly in the constant coefficient. -/
namespace Blotto.PlayerSpecificZeroUniformAffineCDF
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def base (z : ℝ) : ℝ := (Measure.dirac (0:ℝ)).real (Set.Iic z)
noncomputable def slope (ell z : ℝ) : ℝ := ((uniformLaw ell).real (Set.Iic z)-base z)/ell

theorem formula (ell resource z : ℝ) (hell : 0 < ell) (hr : 0 ≤ resource ∧ resource ≤ ell) :
    (zeroUniformLaw ell (resource/ell)).real (Set.Iic z)=base z+slope ell z*resource := by
  let atom : ProbabilityMeasure ℝ := ⟨Measure.dirac 0,inferInstance⟩
  have hq : 0 ≤ resource/ell ∧ resource/ell ≤ 1 :=
    ⟨div_nonneg hr.1 hell.le,(div_le_one hell).mpr hr.2⟩
  have h := PlayerSpecificNestedAffineCDF.affine_event (resource/ell) hq (uniformMarginal ell hell) atom (Set.Iic z)
  change (affineMeasure (resource/ell) (uniformLaw ell) (Measure.dirac 0)).real (Set.Iic z)=
    (resource/ell)*(uniformLaw ell).real (Set.Iic z)+(1-resource/ell)*(Measure.dirac (0:ℝ)).real (Set.Iic z) at h
  have he : zeroUniformLaw ell (resource/ell)=affineMeasure (resource/ell) (uniformLaw ell) (Measure.dirac 0) := by
    unfold zeroUniformLaw affineMeasure
    exact add_comm _ _
  rw [he,h]
  unfold slope base
  ring

end Blotto.PlayerSpecificZeroUniformAffineCDF
