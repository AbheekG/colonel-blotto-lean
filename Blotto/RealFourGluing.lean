import Blotto.RealSegmentFlat
import Blotto.FourGluingDescriptor
import Blotto.RealFourCompiledDescriptor

/-! Exact continuous execution of the finite four-variable gluing table.
Inactive entries retain the budget-row fallback, without a coordinate-box
claim for zero-probability paths. -/

namespace Blotto.FourInput
open MeasureTheory

noncomputable def realGluingSample (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (seed : Fin 81 → ℝ) : Allocation 4 :=
  (i.compiledRealGluingDescriptor hcase).realSampleFlat 0 seed

theorem realGluingSample_refines (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.realGluingSample hcase = (i.gluingDescriptor hcase).realSampleFlat 0 := by
  funext seed
  unfold realGluingSample
  rw [i.compiledRealGluingDescriptor_eq]

theorem realGluingSample_measurable (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    Measurable (i.realGluingSample hcase) := by
  rw [i.realGluingSample_refines]
  exact (i.gluingDescriptor hcase).realSampleFlat_measurable 0

theorem realGluingSample_law (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    Measure.map (i.realGluingSample hcase) (RealUniformInputs.law 81 : Measure (Fin 81 → ℝ)) =
      (i.gluingCaseLaw hcase : Measure (Allocation 4)) := by
  rw [i.realGluingSample_refines]
  exact ((i.gluingDescriptor hcase).realSampleFlat_law 0).trans (i.gluingDescriptor_law hcase)

theorem realGluingSample_fullBudget (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (seed : Fin 81 → ℝ) (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : FullBudget i.B (i.realGluingSample hcase seed) := by
  rw [i.realGluingSample_refines]
  exact (i.gluingDescriptor hcase).realSampleFlat_fullBudget 0 (i.gluingDescriptor_endpoints hcase).1
    (i.gluingDescriptor_endpoints hcase).2 seed ht

theorem realGluingSample_read_labels (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w)
    (seed : Fin 81 → ℝ) :
    ((realCategoricalMachine (0 : Fin 81)).run 80
      (.remaining (realWeightTable (i.gluingDescriptor hcase).weight (i.gluingDescriptor hcase).nonnegative))
      (Fin.tail seed)).2 + 1 ≤ 81 :=
  (i.gluingDescriptor hcase).realSampleFlat_read_labels 0 seed

end Blotto.FourInput
