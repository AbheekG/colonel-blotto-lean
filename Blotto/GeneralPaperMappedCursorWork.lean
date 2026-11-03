import Blotto.GeneralPaperScalarCursorWork

/-! Source-to-scalar mapping, extraction and directory lifting are charged
once. Rational/natural array and control-list instances reuse the actual
measured schema, preserving the sum of source encodings and the suffix. -/
namespace Blotto.GeneralPaperMappedCursorWork
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem mapped_array {α : Type*} {n : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (lift : α → Scalar) (source : FixedArrayTable n α) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (A * (64 + (source.data.toList.map lift).length) +
      ((source.data.toList.map lift).map encode).sum) < 2 ^ A) :
    (GeneralPaperFieldDirectoryParsers.fromArray S A
      (GeneralPaperMappedScalarArrayCursor.run S A lift source
        ((GeneralPaperSequentialLayout.run model S A start
          (A * (64 + (source.data.toList.map lift).length) :: (source.data.toList.map lift).map encode)).1 ++ rest))).work ≤
      (A * (64 + (source.data.toList.map lift).length) + ((source.data.toList.map lift).map encode).sum + 1) *
        16 * unit model S A := by
  let values := source.data.toList.map lift
  let regions := (GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: values.map encode)).1 ++ rest
  let fields := GeneralPaperMappedScalarArrayCursor.expected model S A start values
  have hSome : (GeneralPaperMappedScalarArrayCursor.run S A lift source regions).values = some fields := by
    rw [GeneralPaperMappedScalarArrayCursor.run_values]
    exact (GeneralPaperScalarArrayFieldCursor.layout_success model S A start values rest).1
  have hFrom := GeneralPaperFieldDirectoryParsers.from_array_work S A
    (GeneralPaperMappedScalarArrayCursor.run S A lift source regions) fields hSome
  have hFormula := GeneralPaperMappedScalarArrayCursor.run_work S A lift source regions
  have hSum : source.data.toList.map (fun value => encode (lift value)) = values.map encode := by
    simp only [values,List.map_map,Function.comp_def]
  rw [hSum] at hFormula
  have hLength : values.length = n := by simp only [values,List.length_map,Array.length_toList,source.size]
  have hCounter : n + 1 = values.length + 1 := by omega
  rw [hCounter] at hFormula
  have hScalar := GeneralPaperScalarCursorWork.array_layout model S A start values rest hA hCap
  change (GeneralPaperScalarArrayFieldCursor.run S A values regions).work ≤ _ at hScalar
  have hHeader : GeneralPaperLastRegionSelection.price S A fields.header.region ≤ unit model S A := by
    apply region_work model S A _ hA
    change start + A * (64 + values.length) < 2 ^ A
    change start + (A * (64 + values.length) + (values.map encode).sum) < 2 ^ A at hCap
    omega
  have hMeta := metadata model S A
  have hCount := GeneralPaperScalarCursorWork.count_le_payload values
  have hControl := Nat.mul_le_mul_left (values.length + 1) (show 64 * (S + A + 1) ≤ unit model S A by omega)
  have hPay := Nat.mul_le_mul_left (values.map encode).sum hMeta.1
  have hOther := Nat.mul_le_mul_right (unit model S A)
    (show (values.map encode).sum + values.length + 4 ≤ 8 * (A * (64 + values.length) + (values.map encode).sum + 1) by omega)
  change (GeneralPaperFieldDirectoryParsers.fromArray S A (GeneralPaperMappedScalarArrayCursor.run S A lift source regions)).work ≤
    (A * (64 + values.length) + (values.map encode).sum + 1) * 16 * unit model S A
  rw [hFrom,hFormula]
  change (values.map encode).sum + (values.length + 1) * (64 * (S + A + 1)) +
    (GeneralPaperScalarArrayFieldCursor.run S A values regions).work + 64 * (S + A + 1) +
    GeneralPaperLastRegionSelection.price S A fields.header.region + 64 * (S + A + 1) ≤ _
  nlinarith only [hScalar,hHeader,hControl,hPay,hOther,hMeta.2.1]

theorem rational {n : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable n ℚ) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes.sum < 2 ^ A) :
    (GeneralPaperFieldDirectoryParsers.rational S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source)).1 ++ rest)).work ≤
      ((GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source).sizes.sum + 1) * 16 * unit model S A := by
  rw [GeneralPaperMappedScalarArrayCursor.rational_plan] at hCap
  have h := mapped_array model S A start Scalar.rational source rest hA hCap
  simpa only [GeneralPaperFieldDirectoryParsers.rational,GeneralPaperMeasuredBlockLayout.run,
    GeneralPaperMappedScalarArrayCursor.rational_plan,List.sum_cons] using h

theorem natural {n : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable n ℕ) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes.sum < 2 ^ A) :
    (GeneralPaperFieldDirectoryParsers.natural S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source)).1 ++ rest)).work ≤
      ((GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source).sizes.sum + 1) * 16 * unit model S A := by
  rw [GeneralPaperMappedScalarArrayCursor.natural_plan] at hCap
  have h := mapped_array model S A start Scalar.natural source rest hA hCap
  simpa only [GeneralPaperFieldDirectoryParsers.natural,GeneralPaperMeasuredBlockLayout.run,
    GeneralPaperMappedScalarArrayCursor.natural_plan,List.sum_cons] using h

theorem naturals (model : RationalCostModel) (S A start : ℕ) (values : List ℕ) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (A * (values.length + 32) + (values.map GeneralPaperEncodedScalarStorage.natBits).sum) < 2 ^ A) :
    (GeneralPaperScalarRecordComponents.naturals S A values
      ((GeneralPaperSequentialLayout.run model S A start
        (A * (values.length + 32) :: values.map GeneralPaperEncodedScalarStorage.natBits)).1 ++ rest)).work ≤
      (A * (values.length + 32) + (values.map GeneralPaperEncodedScalarStorage.natBits).sum + 1) * 16 * unit model S A := by
  have hEnc : (values.map Scalar.natural).map encode = values.map GeneralPaperEncodedScalarStorage.natBits := by
    simp only [List.map_map,Function.comp_def,encode]
  have hList := GeneralPaperScalarCursorWork.list_layout model S A start 32 1 (values.map Scalar.natural) rest hA
    (by simpa only [List.length_map,hEnc,Nat.one_mul] using hCap)
  simp only [List.length_map,hEnc,Nat.one_mul] at hList
  have hCount := GeneralPaperScalarCursorWork.count_le_payload (values.map Scalar.natural)
  rw [List.length_map,hEnc] at hCount
  have hMeta := metadata model S A
  have hControl := Nat.mul_le_mul_left (values.length + 1) (show 64 * (S + A + 1) ≤ unit model S A by omega)
  have hPay := Nat.mul_le_mul_left (values.map GeneralPaperEncodedScalarStorage.natBits).sum hMeta.1
  have hOther := Nat.mul_le_mul_right (unit model S A)
    (show (values.map GeneralPaperEncodedScalarStorage.natBits).sum + values.length + 2 ≤
      8 * (A * (values.length + 32) + (values.map GeneralPaperEncodedScalarStorage.natBits).sum + 1) by omega)
  simp only [GeneralPaperScalarRecordComponents.naturals,GeneralPaperScalarRecordComponents.lift_data,
    GeneralPaperScalarRecordComponents.lift_work,encode]
  nlinarith only [hList,hControl,hPay,hOther,hMeta.2.1]

theorem naturals_plan (model : RationalCostModel) (S A start : ℕ) (values : List ℕ) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values).sizes.sum < 2 ^ A) :
    (GeneralPaperScalarRecordComponents.naturals S A values
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values)).1 ++ rest)).work ≤
      ((GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values).sizes.sum + 1) * 16 * unit model S A := by
  simp only [GeneralPaperMeasuredBlockLayout.run,GeneralPaperScalarRecordComponents.natural_plan,
    List.length_map,List.map_map,Function.comp_def,encode,Nat.one_mul,List.sum_cons] at hCap ⊢
  exact naturals model S A start values rest hA hCap

end Blotto.GeneralPaperMappedCursorWork
