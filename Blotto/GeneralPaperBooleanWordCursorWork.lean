import Blotto.GeneralPaperFrontCursorWork

/-! Actual bit-list, retained-word and labelled-row extraction costs. The
stored bits are copied and consumed directly; no integer re-encoding or
external field directory is supplied to these concrete cursor theorems. -/
namespace Blotto.GeneralPaperBooleanWordCursorWork
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork GeneralPaperChildCursorWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem bits (model : RationalCostModel) (S A start : ℕ) (values : List Bool) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (GeneralPaperBooleanWordCursor.bitsSchema model S A values).sum < 2 ^ A) :
    (GeneralPaperBooleanWordCursor.bitsRun S A values
      ((GeneralPaperSequentialLayout.run model S A start (GeneralPaperBooleanWordCursor.bitsSchema model S A values)).1 ++ rest)).work ≤
      ((GeneralPaperBooleanWordCursor.bitsSchema model S A values).sum + 1) * 16 * unit model S A := by
  have hRaw : start + (A * (2 * (values.map Scalar.bit).length + 32) + ((values.map Scalar.bit).map encode).sum) < 2 ^ A := by
    simpa only [GeneralPaperBooleanWordCursor.bits_plan,List.sum_cons] using hCap
  have hList := GeneralPaperScalarCursorWork.list_layout model S A start 32 2 (values.map Scalar.bit) rest hA hRaw
  have hCount := GeneralPaperScalarCursorWork.count_le_payload (values.map Scalar.bit)
  rw [List.length_map] at hCount
  have hMeta := metadata model S A
  have hControl := Nat.mul_le_mul_left (values.length + 1) (show 64 * (S + A + 1) ≤ unit model S A by omega)
  have hPay := Nat.mul_le_mul_left ((values.map Scalar.bit).map encode).sum hMeta.1
  have hOther := Nat.mul_le_mul_right (unit model S A)
    (show ((values.map Scalar.bit).map encode).sum + values.length + 2 ≤
      8 * (A * (2 * (values.map Scalar.bit).length + 32) + ((values.map Scalar.bit).map encode).sum + 1) by omega)
  rw [GeneralPaperBooleanWordCursor.bits_plan]
  simp only [GeneralPaperBooleanWordCursor.bitsRun,GeneralPaperScalarRecordComponents.lift_data,
    GeneralPaperScalarRecordComponents.lift_work,List.sum_cons]
  have hSum : (values.map (fun value => encode (Scalar.bit value))).sum = ((values.map Scalar.bit).map encode).sum := by
    simp only [List.map_map,Function.comp_def]
  rw [hSum]
  nlinarith only [hList,hControl,hPay,hOther,hMeta.2.1]

theorem word {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedBinaryWord w) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.word model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperBooleanWordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.word model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredLeafPlans.word model S A source).sizes.sum + 1) * 48 * unit model S A := by
  have hParser : Correct model S A (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
      (fun _ start => GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits)
      (fun _ => GeneralPaperBooleanWordCursor.bitsRun S A source.bits) := by
    intro value start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperBooleanWordCursor.bits_success model S A start source.bits rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 16 (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
      (fun _ => GeneralPaperBooleanWordCursor.bitsRun S A source.bits) := by
    intro value start rest hCap
    exact bits model S A start source.bits rest hA hCap
  have hPos : ∀ value : Unit,∀ size ∈ GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits,0 < size := by
    intro value
    exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ source.bits hA (by omega)
      (fun _ _ => GeneralPaperEqualMeasuredPlanPositive.tag S)
  rw [GeneralPaperBooleanWordCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 16 (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsRun S A source.bits)
    (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
    (fun _ start => GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits)
    hParser hPrice hPos hA start 16 [()] rest (by decide) hCap
  simpa only [GeneralPaperBooleanWordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperBooleanWordCursor.plan,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

theorem row {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : Fin r × FixedBinaryWord w)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.row model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperBooleanRowCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.row model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredLeafPlans.row model S A source).sizes.sum + 1) * 80 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperBooleanRowCursor.schema model S A source)
      (GeneralPaperBooleanRowCursor.child model S A source) (GeneralPaperBooleanRowCursor.parser S A source) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperBooleanRowCursor.field_success model S A source field start rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 48 (GeneralPaperBooleanRowCursor.schema model S A source) (GeneralPaperBooleanRowCursor.parser S A source) := by
    intro field start rest hCap
    cases field with
    | label =>
      simp only [GeneralPaperBooleanRowCursor.schema,GeneralPaperBooleanRowCursor.parser,
        GeneralPaperMeasuredBlockPlan.natural_data,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
      exact raise model S A _ 3 48 _ (GeneralPaperScalarCursorWork.leaf_layout model S A start (.natural source.1.val) rest hA hCap) (by decide)
    | word => exact word model S A start source.2 rest hA hCap
  have hPos : ∀ field,∀ size ∈ GeneralPaperBooleanRowCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | label => exact GeneralPaperMeasuredPlanPositive.natural model S source.1.val
    | word => exact GeneralPaperEqualMeasuredPlanPositive.word model S A source.2 hA
  rw [GeneralPaperBooleanRowCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 48 (GeneralPaperBooleanRowCursor.parser S A source)
    (GeneralPaperBooleanRowCursor.schema model S A source) (GeneralPaperBooleanRowCursor.child model S A source)
    hParser hPrice hPos hA start 16 GeneralPaperBooleanRowCursor.fields rest (by decide) hCap
  simpa only [GeneralPaperBooleanRowCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperBooleanRowCursor.plan,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

end Blotto.GeneralPaperBooleanWordCursorWork
