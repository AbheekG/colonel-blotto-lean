import Blotto.RealNestedResourceLaw
import Blotto.FourReflectionRecovery
import Blotto.RealFourFactory

/-! Exact execution of the atom-conditioning four-variable branch. One
fresh threshold selects a uniform split or a reflected resource sampler. -/

namespace Blotto
open MeasureTheory
open scoped Classical

namespace MergeFourInput

noncomputable def realSample (i : MergeFourInput) (seed : Fin 9 → ℝ) : Allocation 4 :=
  splitFirstTwo i.l0 i.l1 (i.childSpec.realSample seed)

theorem realSample_measurable (i : MergeFourInput) : Measurable i.realSample :=
  (measurable_splitFirstTwo i.l0 i.l1).comp i.childSpec.realSample_measurable

theorem realSample_law (i : MergeFourInput) :
    Measure.map i.realSample (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) =
      (i.law : Measure (Allocation 4)) := by
  change Measure.map (splitFirstTwo i.l0 i.l1 ∘ i.childSpec.realSample) _ = _
  rw [← Measure.map_map (measurable_splitFirstTwo i.l0 i.l1) i.childSpec.realSample_measurable,
    i.childSpec.realSample_law]
  rfl

theorem realSample_fullBudget (i : MergeFourInput) (seed : Fin 9 → ℝ)
    (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : FullBudget i.B (i.realSample seed) :=
  splitFirstTwo_fullBudget i.l0_pos i.l1_pos (i.childSpec.realSample_fullBudget seed ht)

end MergeFourInput
namespace FourInput

noncomputable def realSmallUniformSample (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : Allocation 4 :=
  ((RealFourParameterTable.prepare i).smallUniformInput hcase).realSample (RealUniformInputs.dropInputs 9 2 seed.2)

theorem realSmallUniformSample_refines (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.realSmallUniformSample hcase = fun seed =>
      (i.smallUniformInput hcase).realSample (RealUniformInputs.dropInputs 9 2 seed.2) := by
  funext seed
  unfold realSmallUniformSample
  rw [RealFourParameterTable.smallUniformInput_eq]

theorem realSmallUniformSample_measurable (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    Measurable (i.realSmallUniformSample hcase) := by
  rw [i.realSmallUniformSample_refines]
  have hTail : Measurable (Prod.snd : ((Fin 2 → ℝ) × (Fin 11 → ℝ)) → (Fin 11 → ℝ)) := measurable_snd
  have hDraw := (i.smallUniformInput hcase).realSample_measurable.comp
    ((RealUniformInputs.dropInputs_measurable 9 2).comp hTail)
  exact hDraw

theorem realSmallUniformSample_law (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    Measure.map (i.realSmallUniformSample hcase)
      (NestedResourceSystem.realInputLaw : Measure ((Fin 2 → ℝ) × (Fin 11 → ℝ))) =
      (i.smallUniformLaw hcase : Measure (Allocation 4)) := by
  rw [i.realSmallUniformSample_refines]
  let j := i.smallUniformInput hcase
  change Measure.map (j.realSample ∘ (RealUniformInputs.dropInputs 9 2 ∘
    (Prod.snd : ((Fin 2 → ℝ) × (Fin 11 → ℝ)) → (Fin 11 → ℝ))))
      ((RealUniformInputs.law 2 : Measure (Fin 2 → ℝ)).prod (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ))) = _
  rw [← Measure.map_map j.realSample_measurable ((RealUniformInputs.dropInputs_measurable 9 2).comp measurable_snd),
    ← Measure.map_map (RealUniformInputs.dropInputs_measurable 9 2) measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul, RealUniformInputs.dropInputs_law 9 2]
  exact j.realSample_law

theorem realSmallUniformSample_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) (h : ∀ j, 0 ≤ seed.2 j ∧ seed.2 j ≤ 1) :
    FullBudget i.B (i.realSmallUniformSample hcase seed) := by
  rw [i.realSmallUniformSample_refines]
  exact (i.smallUniformInput hcase).realSample_fullBudget _ (RealUniformInputs.dropInputs_bounds 9 2 seed.2 h 0)

noncomputable def realReflectedSample (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : Allocation 4 :=
  reflectAppend i.originalLengths (((RealFourParameterTable.prepare i).reflectedResourceSystem hcase).realSample seed)

theorem realReflectedSample_refines (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    i.realReflectedSample hcase = reflectAppend i.originalLengths ∘ (i.reflectedResourceSystem hcase).realSample := by
  funext seed
  unfold realReflectedSample
  rw [RealFourParameterTable.reflectedResourceSystem_eq]
  rfl

theorem realReflectedSample_measurable (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    Measurable (i.realReflectedSample hcase) := by
  rw [i.realReflectedSample_refines]
  exact (measurable_reflectAppend i.originalLengths).comp (i.reflectedResourceSystem hcase).realSample_measurable

theorem realReflectedSample_law (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    Measure.map (i.realReflectedSample hcase)
      (NestedResourceSystem.realInputLaw : Measure ((Fin 2 → ℝ) × (Fin 11 → ℝ))) =
      (i.reflectedZeroLaw hcase : Measure (Allocation 4)) := by
  rw [i.realReflectedSample_refines]
  rw [← Measure.map_map (measurable_reflectAppend i.originalLengths) (i.reflectedResourceSystem hcase).realSample_measurable,
    (i.reflectedResourceSystem hcase).realSample_law]
  rfl

theorem realReflectedSample_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) (h : ∀ j, 0 ≤ seed.2 j ∧ seed.2 j ≤ 1) :
    FullBudget i.B (i.realReflectedSample hcase seed) := by
  rw [i.realReflectedSample_refines]
  have hS : ∑ j, i.originalLengths j = i.B + i.reflectedBudget := by
    rw [i.originalLengths_sum, (i.reflected_budget_bounds hcase).2]
    ring
  exact reflectAppend_fullBudget hS ((i.reflectedResourceSystem hcase).realSample_fullBudget seed h)
    ((i.reflectedResourceSystem hcase).realSample_inBox seed h)

noncomputable def realSmallInputLaw : ProbabilityMeasure (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))) :=
  RealUniformInputs.productLaw unitUniform NestedResourceSystem.realInputLaw

noncomputable def realSmallSample (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))) : Allocation 4 :=
  if seed.1 ≤ i.p then i.realSmallUniformSample hcase seed.2 else i.realReflectedSample hcase seed.2

theorem realSmallSample_measurable (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    Measurable (i.realSmallSample hcase) :=
  RealIndependentChoice.measurable_sample i.p _ _ (i.realSmallUniformSample_measurable hcase) (i.realReflectedSample_measurable hcase)

theorem realSmallSample_law (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    Measure.map (i.realSmallSample hcase)
      (realSmallInputLaw : Measure (ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ)))) =
      (i.smallCaseLaw hcase : Measure (Allocation 4)) := by
  change Measure.map (RealIndependentChoice.sample i.p (i.realSmallUniformSample hcase) (i.realReflectedSample hcase))
    ((unitUniform : Measure ℝ).prod (NestedResourceSystem.realInputLaw : Measure ((Fin 2 → ℝ) × (Fin 11 → ℝ)))) = _
  rw [RealIndependentChoice.map_product i.p ⟨i.p_pos.le, i.p_lt.le⟩ NestedResourceSystem.realInputLaw _ _
    (i.realSmallUniformSample_measurable hcase) (i.realReflectedSample_measurable hcase),
    i.realSmallUniformSample_law hcase, i.realReflectedSample_law hcase]
  exact (binaryLaw_measure i.p _ (i.smallUniformLaw hcase) (i.reflectedZeroLaw hcase)).symm

theorem realSmallSample_fullBudget (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (seed : ℝ × ((Fin 2 → ℝ) × (Fin 11 → ℝ))) (h : ∀ j, 0 ≤ seed.2.2 j ∧ seed.2.2 j ≤ 1) :
    FullBudget i.B (i.realSmallSample hcase seed) := by
  unfold realSmallSample
  split_ifs
  · exact i.realSmallUniformSample_fullBudget hcase seed.2 h
  · exact i.realReflectedSample_fullBudget hcase seed.2 h

end FourInput
end Blotto
