import Blotto.PlayerSpecificCoordinateMapCDF
import Blotto.PlayerSpecificAlgebraicTerminalEmbedding

/-! Whole-law meanings of the two actual four-slot terminal embeddings.
Their zero padding preserves marginal CDF error. -/
namespace Blotto.PlayerSpecificTerminalEmbeddingLaw
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def uniform (y : Allocation 3) : Allocation 4 := ![y 0,y 1,y 2,0]
noncomputable def mixed (y : Allocation 3) : Allocation 4 := ![y 0,y 1,0,y 2]

theorem measurable_uniform : Measurable uniform := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp only [uniform] <;> fun_prop

theorem measurable_mixed : Measurable mixed := by
  apply Measurable.of_eval
  intro j
  fin_cases j <;> simp only [mixed] <;> fun_prop

theorem uniform_CDF (u l : Mixed 3) (E : ℝ) (h : CDFClose u l E) : CDFClose (u.map uniform) (l.map uniform) E := by
  apply PlayerSpecificCoordinateMapCDF.CDF_error uniform measurable_uniform ![0,1,2,0] (fun _ => 0) ![1,1,1,0] _ u l E h
  intro y j
  fin_cases j <;> simp [uniform,affineLine]

theorem mixed_CDF (u l : Mixed 3) (E : ℝ) (h : CDFClose u l E) : CDFClose (u.map mixed) (l.map mixed) E := by
  apply PlayerSpecificCoordinateMapCDF.CDF_error mixed measurable_mixed ![0,1,0,2] (fun _ => 0) ![1,1,0,1] _ u l E h
  intro y j
  fin_cases j <;> simp [mixed,affineLine]

theorem uniform_marginal (l : Mixed 3) (j : Fin 3) : marginal (l.map uniform) j.castSucc=marginal l j := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y : Allocation 4 => y j.castSucc) (Measure.map uniform (l : Measure (Allocation 3)))=_
  rw [Measure.map_map (measurable_pi_apply j.castSucc) measurable_uniform]
  congr 1
  funext y
  fin_cases j <;> rfl

theorem mixed_first (l : Mixed 3) (j : Fin 2) :
    marginal (l.map mixed) j.castSucc.castSucc=marginal l j.castSucc := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y : Allocation 4 => y j.castSucc.castSucc) (Measure.map mixed (l : Measure (Allocation 3)))=_
  rw [Measure.map_map (measurable_pi_apply _) measurable_mixed]
  congr 1
  funext y
  fin_cases j <;> rfl

theorem mixed_last (l : Mixed 3) : marginal (l.map mixed) 3=marginal l 2 := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun y : Allocation 4 => y 3) (Measure.map mixed (l : Measure (Allocation 3)))=_
  rw [Measure.map_map (measurable_pi_apply _) measurable_mixed]
  rfl

end Blotto.PlayerSpecificTerminalEmbeddingLaw
