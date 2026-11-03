import Blotto.PlayerSpecificResourceContinuationCDF
import Blotto.NestedResourceSystem

/-! The terminal nested marginal CDF is affine in its maintained resource.
The same formula holds at the initial resource for the exact coupling. -/
namespace Blotto.PlayerSpecificNestedAffineCDF
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem affine_event (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (u l : ProbabilityMeasure ℝ) (A : Set ℝ) :
    (affineMeasure q (u : Measure ℝ) (l : Measure ℝ)).real A=
      q*(u : Measure ℝ).real A+(1-q)*(l : Measure ℝ).real A := by
  rw [affineMeasure,measureReal_add_apply (by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ A)) (by
      rw [Measure.smul_apply]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ A)),
    measureReal_ennreal_smul_apply,measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal hq.1,ENNReal.toReal_ofReal (sub_nonneg.mpr hq.2)]

noncomputable def base (i : NestedResourceSystem) (j : Fin 3) (z : ℝ) : ℝ := (uniformLaw (i.long j)).real (Set.Iic z)
noncomputable def slope (i : NestedResourceSystem) (j : Fin 3) (z : ℝ) : ℝ :=
  ((uniformLaw (i.short j)).real (Set.Iic z)-(uniformLaw (i.long j)).real (Set.Iic z))/i.capacity j

theorem formula (i : NestedResourceSystem) (r : Allocation 3) (hr : InBox i.capacity r) (l : Mixed 3)
    (hm : ∀ j,(marginal l j : Measure ℝ)=affineMeasure (r j/i.capacity j) (uniformLaw (i.short j)) (uniformLaw (i.long j)))
    (j : Fin 3) (z : ℝ) : closedCDF l j z=base i j z+slope i j z*r j := by
  have hcap : 0 < i.capacity j := sub_pos.mpr (i.short_lt j)
  have hq : 0 ≤ r j/i.capacity j ∧ r j/i.capacity j ≤ 1 :=
    ⟨div_nonneg (hr j).1 hcap.le,(div_le_one hcap).mpr (hr j).2⟩
  unfold closedCDF
  rw [hm j]
  have h := affine_event (r j/i.capacity j) hq (uniformMarginal (i.short j) (i.short_pos j))
    (uniformMarginal (i.long j) (lt_trans (i.short_pos j) (i.short_lt j))) (Set.Iic z)
  change (affineMeasure (r j/i.capacity j) (uniformLaw (i.short j)) (uniformLaw (i.long j))).real (Set.Iic z)=
    (r j/i.capacity j)*(uniformLaw (i.short j)).real (Set.Iic z)+
      (1-r j/i.capacity j)*(uniformLaw (i.long j)).real (Set.Iic z) at h
  rw [h]
  unfold base slope
  ring

theorem initial (i : NestedResourceSystem) (j : Fin 3) (z : ℝ) :
    closedCDF i.law j z=base i j z+slope i j z*i.initial j :=
  formula i i.initial i.initial_box i.law i.law_contract.2 j z

theorem terminal (i : NestedResourceSystem) (r : Allocation 3) (hr : i.Valid r) (j : Fin 3) (z : ℝ) :
    closedCDF (i.terminal r hr).law j z=base i j z+slope i j z*r j :=
  formula i r hr.1 (i.terminal r hr).law (i.terminal r hr).law_contract.2 j z

end Blotto.PlayerSpecificNestedAffineCDF
