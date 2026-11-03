import Blotto.GeneralPaperBooleanWordCursorWork

/-! Complete labelled-row-list, ruler-count and Boolean-cache extraction.
The ruler's actual source scan and fixed-width count encoding are charged
to its allocated header area, including empty-payload source elements. -/
namespace Blotto.GeneralPaperBooleanCacheCursorWork
open GeneralPaperSequentialLayout GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperDirectoryCopyWork GeneralPaperChildCursorWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem encoding_step (model : RationalCostModel) (S A : ℕ) :
    GeneralPaperStoredWordEncoding.stepBound model S A (A + 8) ≤ unit model S A := by
  have hw : binaryWordWidth (A + 1) ≤ A + 2 := by have h := Nat.log2_le_self (A + 1); unfold binaryWordWidth; omega
  have hRat := model.monotone (show A + 8 + 4 ≤ 8 * (A + 9) by omega)
  unfold GeneralPaperStoredWordEncoding.stepBound unit
  omega

theorem ruler (model : RationalCostModel) (S A start : ℕ) (source : List Unit) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes.sum < 2 ^ A) :
    (GeneralPaperRulerFieldCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)).1 ++ rest)).work ≤
      ((GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes.sum + 1) * 8 * unit model S A := by
  have hCountFits := GeneralPaperRulerFieldCursor.count_fits model S A start source hA hCap
  have hWidth := binaryWordWidth_le_of_lt_pow hA hCountFits
  have hZero : (source.map (fun value => (GeneralPaperEqualMeasuredLeafPlans.unit S value).sizes.sum)).sum = 0 := by
    simp [GeneralPaperEqualMeasuredLeafPlans.unit,GeneralPaperEqualMeasuredLeafPlans.empty]
  have hBody := GeneralPaperMeasuredListPlanWork.body_work model S A 1 (GeneralPaperEqualMeasuredLeafPlans.unit S) source hA
    (fun _ _ => GeneralPaperMeasuredLeafPlanWork.empty model S A) (by omega) (by rw [hZero]; positivity)
  rw [hZero] at hBody
  have hEncoding := GeneralPaperStoredWordEncoding.work model S A source.length (A + 8) (by omega)
  have hEncodeStep := Nat.mul_le_mul_left A (encoding_step model S A)
  have hCapRaw : start + A * (2 * source.length + 32) < 2 ^ A := by
    simpa only [GeneralPaperRulerFieldCursor.plan,List.sum_cons,List.sum_nil,Nat.add_zero] using hCap
  let header := GeneralPaperScalarRecordComponents.listHeader A start 32 2 source.length
  have hHeader := region_work model S A header hA hCapRaw
  have hN : source.length ≤ A * (2 * source.length + 32) := by
    have h := Nat.mul_le_mul_right (2 * source.length + 32) hA
    nlinarith only [h]
  have hAOwn : A ≤ A * (2 * source.length + 32) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left A (show 1 ≤ 2 * source.length + 32 by omega)
  have hOther := Nat.mul_le_mul_right (unit model S A)
    (show 4 * (source.length + 1) + A + 3 ≤ 8 * (A * (2 * source.length + 32) + 1) by omega)
  have hMeta := metadata model S A
  have hBase : 64 * S + 64 ≤ unit model S A := by omega
  have hStream : (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)).1 = [header] := by
    simp only [GeneralPaperMeasuredBlockLayout.run,GeneralPaperRulerFieldCursor.plan,GeneralPaperSequentialLayout.run,
      GeneralPaperStoredWordEncoding.word_data,header,GeneralPaperScalarRecordComponents.listHeader]
  rw [hStream,List.singleton_append,GeneralPaperRulerFieldCursor.plan]
  simp only [GeneralPaperRulerFieldCursor.run,GeneralPaperMeasuredListBlockPlan.body_count,List.sum_cons,List.sum_nil,Nat.add_zero]
  nlinarith only [hBody,hEncoding,hEncodeStep,hHeader,hOther,hMeta.2.1,hBase]

theorem rows {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : List (Fin r × FixedBinaryWord w))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source).sizes.sum < 2 ^ A) :
    (GeneralPaperBooleanRowCursor.rowsRun S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source)).1 ++ rest)).work ≤
      ((GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source).sizes.sum + 1) * 104 * unit model S A := by
  have hParser : Correct model S A (fun row : Fin r × FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
      (GeneralPaperBooleanRowCursor.expected model S A) (GeneralPaperBooleanRowCursor.run S A) := by
    intro row start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperBooleanRowCursor.success model S A start row rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 80 (fun row : Fin r × FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
      (GeneralPaperBooleanRowCursor.run S A) := by
    intro row start rest hCap
    exact GeneralPaperBooleanWordCursorWork.row model S A start row rest hA hCap
  have hPos : ∀ row : Fin r × FixedBinaryWord w,∀ size ∈ (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes,0 < size := by
    intro row
    exact GeneralPaperEqualMeasuredPlanPositive.row model S A row hA
  rw [GeneralPaperMeasuredListBlockPlan.data] at hCap
  simp only [List.singleton_append] at hCap
  have h := GeneralPaperFrontCursorWork.front model S A 80 (GeneralPaperBooleanRowCursor.run S A)
    (fun row : Fin r × FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
    (GeneralPaperBooleanRowCursor.expected model S A) hParser hPrice hPos hA start source rest hCap
  simpa only [GeneralPaperBooleanRowCursor.rowsRun,GeneralPaperMeasuredBlockLayout.run,
    GeneralPaperMeasuredListBlockPlan.data,List.singleton_append,List.sum_cons] using h

theorem boolean {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    {prepared : GeneralPaperEqualPreparedCache.Prepared G l}
    (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperBooleanRecordCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes.sum + 1) * 136 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperBooleanRecordCursor.schema model S A source)
      (GeneralPaperBooleanRecordCursor.child model S A source) (GeneralPaperBooleanRecordCursor.parser model S A source) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperBooleanRecordCursor.field_success model S A source field start rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 104 (GeneralPaperBooleanRecordCursor.schema model S A source) (GeneralPaperBooleanRecordCursor.parser model S A source) := by
    intro field start rest hCap
    cases field with
    | denominator => exact raise model S A _ 48 104 _ (GeneralPaperBooleanWordCursorWork.word model S A start source.denominator rest hA hCap) (by decide)
    | rows => exact rows model S A start source.rows rest hA hCap
    | ruler => exact raise model S A _ 8 104 _ (ruler model S A start source.ruler rest hA hCap) (by decide)
  have hPos : ∀ field,∀ size ∈ GeneralPaperBooleanRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | denominator => exact GeneralPaperEqualMeasuredPlanPositive.word model S A source.denominator hA
    | rows =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ source.rows hA (by omega)
        (fun value _ => GeneralPaperEqualMeasuredPlanPositive.row model S A value hA)
    | ruler =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ source.ruler hA (by omega)
        (fun _ _ => GeneralPaperEqualMeasuredPlanPositive.empty S)
  rw [GeneralPaperBooleanRecordCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 104 (GeneralPaperBooleanRecordCursor.parser model S A source)
    (GeneralPaperBooleanRecordCursor.schema model S A source) (GeneralPaperBooleanRecordCursor.child model S A source)
    hParser hPrice hPos hA start 64 GeneralPaperBooleanRecordCursor.fields rest (by decide) hCap
  simpa only [GeneralPaperBooleanRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperBooleanRecordCursor.plan,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

end Blotto.GeneralPaperBooleanCacheCursorWork
