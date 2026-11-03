import Blotto.RealSegmentFlat
import Blotto.ThreeLottery
import Blotto.RealThreeInputCompiler

/-! Exact-real execution of the complete three-variable segment table,
including exceptional geometry, zero weights and the ordering swap. -/

namespace Blotto.ThreeSpec
open MeasureTheory

noncomputable def realSample (i : ThreeSpec) (seed : Fin 9 → ℝ) : Allocation 3 :=
  i.compiledRealLottery.realSampleFlat 0 seed

theorem realSample_refines (i : ThreeSpec) (seed : Fin 9 → ℝ) :
    i.realSample seed = i.segmentLottery.realSampleFlat 0 seed := by
  unfold realSample
  rw [i.compiledRealLottery_eq]

theorem realSample_measurable (i : ThreeSpec) : Measurable i.realSample := by
  have hEq : i.realSample = i.segmentLottery.realSampleFlat 0 := funext i.realSample_refines
  rw [hEq]
  exact i.segmentLottery.realSampleFlat_measurable 0

theorem realSample_law (i : ThreeSpec) :
    Measure.map i.realSample (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) =
      (i.law : Measure (Allocation 3)) := by
  have hEq : i.realSample = i.segmentLottery.realSampleFlat 0 := funext i.realSample_refines
  rw [hEq]
  exact (i.segmentLottery.realSampleFlat_law 0).trans i.segmentLottery_law

theorem realSample_marginals (i : ThreeSpec) :
    Measure.map (fun seed => i.realSample seed 0) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) = uniformLaw i.a ∧
      Measure.map (fun seed => i.realSample seed 1) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) = uniformLaw i.d ∧
      Measure.map (fun seed => i.realSample seed 2) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) = zeroUniformLaw i.c i.p := by
  have hCoordinate (j : Fin 3) :
      Measure.map (fun seed => i.realSample seed j) (RealUniformInputs.law 9 : Measure (Fin 9 → ℝ)) =
        (marginal i.law j : Measure ℝ) := by
    change Measure.map ((fun x : Allocation 3 => x j) ∘ i.realSample) _ = _
    rw [← Measure.map_map (measurable_pi_apply j) i.realSample_measurable, i.realSample_law]
    rfl
  rw [hCoordinate 0, hCoordinate 1, hCoordinate 2]
  exact i.law_contract.2

theorem realSample_fullBudget (i : ThreeSpec) (seed : Fin 9 → ℝ)
    (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : FullBudget i.B (i.realSample seed) := by
  rw [i.realSample_refines]
  exact i.segmentLottery.realSampleFlat_fullBudget 0 i.segmentLottery_endpoints.1 i.segmentLottery_endpoints.2 seed ht

theorem realSample_inBox (i : ThreeSpec) (seed : Fin 9 → ℝ)
    (ht : 0 ≤ seed 0 ∧ seed 0 ≤ 1) : InBox ![i.a, i.d, i.c] (i.realSample seed) := by
  rw [i.realSample_refines, SegmentLottery.realSampleFlat_refines]
  exact segment_inBox (i.segmentLottery_box.1 _) (i.segmentLottery_box.2 _) ht

theorem realSample_read_labels (i : ThreeSpec) (seed : Fin 9 → ℝ) :
    ((realCategoricalMachine (0 : Fin 9)).run 8
      (.remaining (realWeightTable i.segmentLottery.weight i.segmentLottery.nonnegative)) (Fin.tail seed)).2 + 1 ≤ 9 :=
  i.segmentLottery.realSampleFlat_read_labels 0 seed

end Blotto.ThreeSpec
