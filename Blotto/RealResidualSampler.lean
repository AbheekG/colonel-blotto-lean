import Blotto.RealSegmentFlat
import Blotto.RealUniformDrop
import Blotto.NestedDyadicFamilies
import Blotto.RealNestedResidualCompiler

/-! The explicit three-segment residual has an exact continuous draw.
A fixed trailing three-input block also gives a ten-input interface. -/

namespace Blotto.NestedResidual
open MeasureTheory

noncomputable def realSample (r : NestedResidual) (seed : Fin 10 → ℝ) : Allocation 3 :=
  (RealNestedResidualCode.compiledLottery r).realSampleFlat 0 (RealUniformInputs.dropInputs 3 7 seed)

theorem realSample_refines (r : NestedResidual) :
    r.realSample = fun seed => r.segmentLottery.realSampleFlat 0 (RealUniformInputs.dropInputs 3 7 seed) := by
  funext seed
  unfold realSample
  rw [RealNestedResidualCode.compiledLottery_eq]

theorem realSample_measurable (r : NestedResidual) : Measurable r.realSample := by
  rw [r.realSample_refines]
  exact (r.segmentLottery.realSampleFlat_measurable 0).comp (RealUniformInputs.dropInputs_measurable 3 7)

theorem realSample_law (r : NestedResidual) :
    Measure.map r.realSample (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) =
      (r.law : Measure (Allocation 3)) := by
  rw [r.realSample_refines]
  change Measure.map (r.segmentLottery.realSampleFlat 0 ∘ RealUniformInputs.dropInputs 3 7) _ = _
  rw [← Measure.map_map (r.segmentLottery.realSampleFlat_measurable 0) (RealUniformInputs.dropInputs_measurable 3 7),
    RealUniformInputs.dropInputs_law 3 7, SegmentLottery.realSampleFlat_law, r.segmentLottery_law]

theorem realSample_fullBudget (r : NestedResidual) (seed : Fin 10 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget r.g.budget (r.realSample seed) := by
  rw [r.realSample_refines]
  exact r.segmentLottery.realSampleFlat_fullBudget 0 (fun _ => r.vertex_fullBudget _) (fun _ => r.vertex_fullBudget _)
    _ (RealUniformInputs.dropInputs_bounds 3 7 seed h 0)

end Blotto.NestedResidual
