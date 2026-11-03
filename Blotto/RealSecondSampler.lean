import Blotto.RealFamilyFirst
import Blotto.RealBinaryFlat
import Blotto.NestedSecond
import Blotto.RealThreeInputCompiler

/-! Exact continuous second nested case, including the deterministic
mirror-length boundary. Its flat interface has eleven independent inputs. -/

namespace Blotto.NestedInput
open MeasureTheory
open scoped Classical

noncomputable def realSecondUniformSample (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) (seed : Fin 10 → ℝ) : Allocation 3 :=
  shiftThird (RationalNestedParametersCode.mirror.realValue (RealNestedParametersCode.environment i 0)) ((i.secondUniformInput htu hTt).compiledRealLottery.realSampleFlat 0 (Fin.tail seed))

theorem realSecondUniformSample_refines (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (seed : Fin 10 → ℝ) : i.realSecondUniformSample htu hTt seed =
      shiftThird i.mirrorLength ((i.secondUniformInput htu hTt).segmentLottery.realSampleFlat 0 (Fin.tail seed)) := by
  unfold realSecondUniformSample
  rw [RealNestedParametersCode.mirror_value, ThreeInput.compiledRealLottery_eq]

theorem realSecondUniformSample_measurable (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    Measurable (i.realSecondUniformSample htu hTt) := by
  have hEq : i.realSecondUniformSample htu hTt =
      shiftThird i.mirrorLength ∘ ((i.secondUniformInput htu hTt).segmentLottery.realSampleFlat 0 ∘
        (Fin.tail : (Fin 10 → ℝ) → (Fin 9 → ℝ))) := funext (i.realSecondUniformSample_refines htu hTt)
  rw [hEq]
  have hDraw := ((i.secondUniformInput htu hTt).segmentLottery.realSampleFlat_measurable 0).comp
    (RealUniformInputs.measurable_tail 9)
  have hCompose := (measurable_shiftThird i.mirrorLength).comp hDraw
  exact hCompose

theorem realSecondUniformSample_law (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    Measure.map (i.realSecondUniformSample htu hTt) (RealUniformInputs.law 10 : Measure (Fin 10 → ℝ)) =
      (i.secondUniformLaw htu hTt : Measure (Allocation 3)) := by
  have hEq : i.realSecondUniformSample htu hTt =
      shiftThird i.mirrorLength ∘ ((i.secondUniformInput htu hTt).segmentLottery.realSampleFlat 0 ∘
        (Fin.tail : (Fin 10 → ℝ) → (Fin 9 → ℝ))) := funext (i.realSecondUniformSample_refines htu hTt)
  rw [hEq]
  let l := (i.secondUniformInput htu hTt).segmentLottery
  change Measure.map (shiftThird i.mirrorLength ∘
    (l.realSampleFlat 0 ∘ (Fin.tail : (Fin 10 → ℝ) → (Fin 9 → ℝ)))) _ = _
  rw [← Measure.map_map (measurable_shiftThird i.mirrorLength)
    ((l.realSampleFlat_measurable 0).comp (RealUniformInputs.measurable_tail 9)),
    ← Measure.map_map (l.realSampleFlat_measurable 0) (RealUniformInputs.measurable_tail 9), RealUniformInputs.tail_law 9]
  rw [l.realSampleFlat_law 0]
  change Measure.map _ ((i.secondUniformInput htu hTt).segmentLottery.law : Measure (Allocation 3)) = _
  rw [ThreeInput.segmentLottery_law]
  rfl

theorem realSecondUniformSample_fullBudget (i : NestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (seed : Fin 10 → ℝ) (ht : 0 ≤ seed 1 ∧ seed 1 ≤ 1) :
    FullBudget i.M (i.realSecondUniformSample htu hTt seed) := by
  rw [i.realSecondUniformSample_refines]
  let j := i.secondUniformInput htu hTt
  have hB : j.B + i.mirrorLength = i.M := by dsimp [j, secondUniformInput]; ring
  have hDraw := j.segmentLottery.realSampleFlat_fullBudget 0
    j.segmentLottery_endpoints.1 j.segmentLottery_endpoints.2 (Fin.tail seed) ht
  change FullBudget i.M (shiftThird i.mirrorLength (j.segmentLottery.realSampleFlat 0 (Fin.tail seed)))
  simpa only [hB] using shiftThird_fullBudget (le_of_lt (i.mirrorLength_bounds htu).1) hDraw

noncomputable def realSecondSample (i : NestedInput) (htu : i.u ≤ i.t) (seed : Fin 11 → ℝ) : Allocation 3 :=
  let mirror := RationalNestedParametersCode.mirror.realValue (RealNestedParametersCode.environment i 0)
  have hMirror : mirror = i.mirrorLength := RealNestedParametersCode.mirror_value i 0
  have hPos : 0 < mirror := by rw [hMirror]; exact (i.mirrorLength_bounds htu).1
  have hV : mirror ≤ i.v := by rw [hMirror]; exact (i.mirrorLength_bounds htu).2.1
  if hTt : mirror < i.t then
    realBinarySample (RationalNestedParametersCode.secondAlpha.realValue (RealNestedParametersCode.environment i 0))
      (i.realFamilyFirstSample mirror hPos hV)
      (i.realSecondUniformSample htu (by simpa only [hMirror] using hTt)) seed
  else i.realFamilyFirstSample mirror hPos hV (Fin.tail seed)

theorem realSecondSample_refines (i : NestedInput) (htu : i.u ≤ i.t) :
    i.realSecondSample htu = fun seed =>
      if hTt : i.mirrorLength < i.t then
        realBinarySample i.secondAlpha
          (i.realFamilyFirstSample i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1)
          (i.realSecondUniformSample htu hTt) seed
      else i.realFamilyFirstSample i.mirrorLength (i.mirrorLength_bounds htu).1
        (i.mirrorLength_bounds htu).2.1 (Fin.tail seed) := by
  funext seed
  simp only [realSecondSample, RealNestedParametersCode.mirror_value, RealNestedParametersCode.secondAlpha_value]
  by_cases hTt : i.mirrorLength < i.t
  · simp only [dite_eq_left hTt]
    congr 1
  · simp only [dite_eq_right hTt]
    exact realFamilyFirstSample_length_congr i _ _ _ _ _ _ (RealNestedParametersCode.mirror_value i 0) (Fin.tail seed)

theorem realSecondSample_measurable (i : NestedInput) (htu : i.u ≤ i.t) : Measurable (i.realSecondSample htu) := by
  rw [i.realSecondSample_refines htu]
  change Measurable (fun seed => if hTt : i.mirrorLength < i.t then _ else _)
  by_cases hTt : i.mirrorLength < i.t
  · simp only [dite_eq_left hTt]
    exact realBinarySample_measurable i.secondAlpha _ _ (i.realFamilyFirstSample_measurable _ _ _)
      (i.realSecondUniformSample_measurable htu hTt)
  · simp only [dite_eq_right hTt]
    exact (i.realFamilyFirstSample_measurable _ _ _).comp (RealUniformInputs.measurable_tail 10)

theorem realSecondSample_law (i : NestedInput) (htu : i.u ≤ i.t) :
    Measure.map (i.realSecondSample htu) (RealUniformInputs.law 11 : Measure (Fin 11 → ℝ)) =
      (i.secondLaw htu : Measure (Allocation 3)) := by
  rw [i.realSecondSample_refines htu]
  change Measure.map (fun seed => if hTt : i.mirrorLength < i.t then _ else _) _ = _
  by_cases hTt : i.mirrorLength < i.t
  · simp only [secondLaw, dite_eq_left hTt]
    exact realBinarySample_realizes i.secondAlpha _ _ _ (i.realFamilyFirstSample_measurable _ _ _)
      (i.realSecondUniformSample_measurable htu hTt) _ _
      (i.realFamilyFirstSample_law _ _ _) (i.realSecondUniformSample_law htu hTt)
  · simp only [secondLaw, dite_eq_right hTt]
    change Measure.map (i.realFamilyFirstSample _ _ _ ∘
      (Fin.tail : (Fin 11 → ℝ) → (Fin 10 → ℝ))) _ = _
    rw [← Measure.map_map (i.realFamilyFirstSample_measurable _ _ _) (RealUniformInputs.measurable_tail 10),
      RealUniformInputs.tail_law 10]
    exact i.realFamilyFirstSample_law _ _ _

theorem realSecondSample_fullBudget (i : NestedInput) (htu : i.u ≤ i.t) (seed : Fin 11 → ℝ)
    (h : ∀ j, 0 ≤ seed j ∧ seed j ≤ 1) : FullBudget i.M (i.realSecondSample htu seed) := by
  rw [i.realSecondSample_refines htu]
  change FullBudget i.M (if hTt : i.mirrorLength < i.t then _ else _)
  split_ifs with hTt
  · exact realBinarySample_predicate _ _ _ seed (FullBudget i.M)
      (i.realFamilyFirstSample_fullBudget _ _ _ (Fin.tail seed) (h 1) (h 2))
      (i.realSecondUniformSample_fullBudget htu hTt (Fin.tail seed) (h 2))
  · exact i.realFamilyFirstSample_fullBudget _ _ _ (Fin.tail seed) (h 1) (h 2)

end Blotto.NestedInput
