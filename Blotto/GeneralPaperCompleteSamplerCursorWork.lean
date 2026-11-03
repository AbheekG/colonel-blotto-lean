import Blotto.GeneralPaperBooleanCacheCursorWork

/-! Complete concrete stored-sampler and dominant-row cursor work. All
generic child prices are discharged. Actual measured schemas, original
budget payloads and untouched suffixes are preserved through the last record. -/
namespace Blotto.GeneralPaperCompleteSamplerCursorWork
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork GeneralPaperChildCursorWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem sampler {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperSamplerRecordCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum + 1) * 168 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperSamplerRecordCursor.schema model S A source)
      (GeneralPaperSamplerRecordCursor.child model S A source) (GeneralPaperSamplerRecordCursor.parser model S A source) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperSamplerRecordCursor.field_success model S A source field start rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 136 (GeneralPaperSamplerRecordCursor.schema model S A source) (GeneralPaperSamplerRecordCursor.parser model S A source) := by
    intro field start rest hCap
    cases field with
    | prepared => exact raise model S A _ 104 136 _ (GeneralPaperPreparedCursorWork.prepared model S A start source.prepared rest hA hCap) (by decide)
    | boolean => exact GeneralPaperBooleanCacheCursorWork.boolean model S A start source.categorical rest hA hCap
    | controls => exact raise model S A _ 16 136 _ (GeneralPaperMappedCursorWork.naturals_plan model S A start (GeneralPaperSamplerRecordCursor.controls source) rest hA hCap) (by decide)
  have hPos : ∀ field,∀ size ∈ GeneralPaperSamplerRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | prepared => exact GeneralPaperEqualMeasuredPlanPositive.prepared model S A source.prepared hA
    | boolean => exact GeneralPaperEqualMeasuredPlanPositive.boolean model S A source.categorical hA
    | controls =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega)
        (fun value _ => GeneralPaperMeasuredPlanPositive.natural model S value)
  rw [GeneralPaperSamplerRecordCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 136 (GeneralPaperSamplerRecordCursor.parser model S A source)
    (GeneralPaperSamplerRecordCursor.schema model S A source) (GeneralPaperSamplerRecordCursor.child model S A source)
    hParser hPrice hPos hA start 64 GeneralPaperSamplerRecordCursor.fields rest (by decide) hCap
  simpa only [GeneralPaperSamplerRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperSamplerRecordCursor.plan,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

theorem dominant {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A) :
    (GeneralPaperStoredDominantCursor.run S A chosen source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen source)).1 ++ rest)).work ≤
      ((GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum + 1) * 48 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperStoredDominantCursor.schema model S A chosen source)
      (GeneralPaperStoredDominantCursor.child model S A chosen source) (GeneralPaperStoredDominantCursor.parser S A chosen source) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperStoredDominantCursor.field_success model S A chosen source field start rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 16 (GeneralPaperStoredDominantCursor.schema model S A chosen source) (GeneralPaperStoredDominantCursor.parser S A chosen source) := by
    intro field start rest hCap
    cases field with
    | row => exact GeneralPaperMappedCursorWork.rational model S A start (GeneralPaperStoredDominantCursor.rowTable source) rest hA hCap
    | chosen =>
      simp only [GeneralPaperStoredDominantCursor.schema,GeneralPaperStoredDominantCursor.parser,
        GeneralPaperMeasuredBlockPlan.natural_data,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
      exact raise model S A _ 3 16 _ (GeneralPaperScalarCursorWork.leaf_layout model S A start (.natural chosen) rest hA hCap) (by decide)
  have hPos : ∀ field,∀ size ∈ GeneralPaperStoredDominantCursor.schema model S A chosen source field,0 < size := by
    intro field
    cases field with
    | row =>
      exact GeneralPaperMeasuredPlanPositive.array model S A _ (GeneralPaperStoredDominantCursor.rowTable source) hA
        (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
    | chosen => exact GeneralPaperMeasuredPlanPositive.natural model S chosen
  rw [GeneralPaperStoredDominantCursor.plan_data] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 16 (GeneralPaperStoredDominantCursor.parser S A chosen source)
    (GeneralPaperStoredDominantCursor.schema model S A chosen source) (GeneralPaperStoredDominantCursor.child model S A chosen source)
    hParser hPrice hPos hA start 32 GeneralPaperStoredDominantCursor.fields rest (by decide) hCap
  simpa only [GeneralPaperStoredDominantCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperStoredDominantCursor.plan_data,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

end Blotto.GeneralPaperCompleteSamplerCursorWork
