import Blotto.GeneralPaperRecordCursorWork

/-! Concrete route, endpoint-matrix, segment and prepared-cache cursors
discharge the erased component premises. Every actual budget field is
copied once per fixed record depth; following regions remain untouched. -/
namespace Blotto.GeneralPaperPreparedCursorWork
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue GeneralPaperFieldDirectorySafety
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork GeneralPaperChildCursorWork
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem trailing_scalar (model : RationalCostModel) (S A start arity : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + ((values.map encode).sum + A * arity) < 2 ^ A) :
    (GeneralPaperTrailingScalarRecord.run S A values
      ((GeneralPaperSequentialLayout.run model S A start (values.map encode ++ [A * arity])).1 ++ rest)).work ≤
      ((values.map encode).sum + A * arity + 1) * 8 * unit model S A := by
  let record := GeneralPaperTrailingScalarRecord.header A (start + (values.map encode).sum) arity
  let regions := (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hRegions := layout_region_work model S A start (⟨values.map encode,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) hA (by change start + (values.map encode).sum < 2 ^ A; omega)
  have hPayload := GeneralPaperScalarCursorWork.on_prefix model S A regions (record :: rest) values hLength hRegions
  have hWork := GeneralPaperTrailingScalarRecord.work_on_prefix S A regions record rest values hLength
  have hRecord := region_work model S A record hA (by change start + (values.map encode).sum + A * arity < 2 ^ A; omega)
  have hCount := GeneralPaperScalarCursorWork.count_le_payload values
  have hMeta := metadata model S A
  have hStep : A + 64 * (S + A + 1) ≤ unit model S A := by unfold unit; omega
  have hTargets := Nat.mul_le_mul_left values.length hStep
  have hControl : 192 * (S + A + 1) ≤ unit model S A := by unfold unit; omega
  have hPay := Nat.mul_le_mul_left (values.map encode).sum hMeta.1
  have hOther := Nat.mul_le_mul_right (unit model S A)
    (show 3 * values.length + 3 ≤ 7 * ((values.map encode).sum + A * arity + 1) by omega)
  rw [GeneralPaperTrailingScalarRecord.layout_regions,List.append_assoc,List.singleton_append]
  change (GeneralPaperTrailingScalarRecord.run S A values (regions ++ record :: rest)).work ≤ _
  rw [hWork]
  nlinarith only [hPayload,hRecord,hTargets,hControl,hPay,hOther,Nat.zero_le ((A * arity) * unit model S A)]

theorem route {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : GroupRoute m) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.route model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperRouteFieldCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.route model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredLeafPlans.route model S A source).sizes.sum + 1) * 16 * unit model S A := by
  rw [GeneralPaperRouteFieldCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := trailing_scalar model S A start 16 (GeneralPaperRouteFieldCursor.values source) rest hA hCap
  have hMeta := metadata model S A
  have hPay := Nat.mul_le_mul_left ((GeneralPaperRouteFieldCursor.values source).map encode).sum hMeta.1
  have hControl : 256 * (S + A + 1) ≤ unit model S A := by unfold unit; omega
  have hOther := Nat.mul_le_mul_right (unit model S A)
    (show ((GeneralPaperRouteFieldCursor.values source).map encode).sum + 1 ≤
      8 * (((GeneralPaperRouteFieldCursor.values source).map encode).sum + A * 16 + 1) by omega)
  rw [GeneralPaperRouteFieldCursor.work,GeneralPaperRouteFieldCursor.plan]
  simp only [GeneralPaperMeasuredBlockLayout.run,GeneralPaperRouteFieldCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero]
  nlinarith only [h,hPay,hControl,hOther]

theorem matrix {m r : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperMatrixFieldCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum + 1) * 40 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperMatrixFieldCursor.rowSchema (m := m) model S A)
      (GeneralPaperMatrixFieldCursor.rowExpected (m := m) model S A) (GeneralPaperFieldDirectoryParsers.rational S A) := by
    intro row start rest
    exact GeneralPaperFieldDirectoryParsers.rational_success model S A start row rest
  have hPrice : Price model S A 16 (GeneralPaperMatrixFieldCursor.rowSchema (m := m) model S A)
      (GeneralPaperFieldDirectoryParsers.rational S A) := by
    intro row start rest hCap
    exact GeneralPaperMappedCursorWork.rational model S A start row rest hA hCap
  have hPos : ∀ row : FixedArrayTable m ℚ,∀ size ∈ GeneralPaperMatrixFieldCursor.rowSchema (m := m) model S A row,0 < size := by
    intro row
    exact GeneralPaperMeasuredPlanPositive.array model S A _ row hA (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
  rw [GeneralPaperMatrixFieldCursor.plan] at hCap
  have h := GeneralPaperRecordCursorWork.nested model S A 16 (GeneralPaperFieldDirectoryParsers.rational S A)
    (GeneralPaperMatrixFieldCursor.rowSchema (m := m) model S A) (GeneralPaperMatrixFieldCursor.rowExpected (m := m) model S A)
    hParser hPrice hPos hA start source.data.toList rest hCap
  simpa only [GeneralPaperMatrixFieldCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperMatrixFieldCursor.plan,List.sum_cons] using h

theorem route_array {n m : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable n (GroupRoute m)) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum < 2 ^ A) :
    (GeneralPaperRouteArrayCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source)).1 ++ rest)).work ≤
      ((GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source).sizes.sum + 1) * 40 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperRouteArrayCursor.schema (m := m) model S A)
      (GeneralPaperRouteFieldCursor.expected (m := m) model S A) (GeneralPaperRouteFieldCursor.run S A) := by
    intro value start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperRouteFieldCursor.success model S A start value rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 16 (GeneralPaperRouteArrayCursor.schema (m := m) model S A) (GeneralPaperRouteFieldCursor.run S A) := by
    intro value start rest hCap
    exact route model S A start value rest hA hCap
  have hPos : ∀ value : GroupRoute m,∀ size ∈ GeneralPaperRouteArrayCursor.schema (m := m) model S A value,0 < size := by
    intro value
    exact GeneralPaperEqualMeasuredPlanPositive.route model S A value hA
  rw [GeneralPaperRouteArrayCursor.plan] at hCap
  have h := GeneralPaperRecordCursorWork.nested model S A 16 (GeneralPaperRouteFieldCursor.run S A)
    (GeneralPaperRouteArrayCursor.schema (m := m) model S A) (GeneralPaperRouteFieldCursor.expected (m := m) model S A)
    hParser hPrice hPos hA start source.data.toList rest hCap
  simpa only [GeneralPaperRouteArrayCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperRouteArrayCursor.plan,List.sum_cons] using h

theorem segments {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (source : PreparedSegmentDescriptor l) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperSegmentRecordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum + 1) * 72 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperSegmentRecordCursor.schema model S A source)
      (GeneralPaperSegmentRecordCursor.child model S A source) (GeneralPaperSegmentRecordCursor.parser S A source) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperSegmentRecordCursor.field_success model S A source field start rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 40 (GeneralPaperSegmentRecordCursor.schema model S A source) (GeneralPaperSegmentRecordCursor.parser S A source) := by
    intro field start rest hCap
    cases field with
    | weights => exact raise model S A _ 16 40 _ (GeneralPaperMappedCursorWork.rational model S A start source.weights rest hA hCap) (by decide)
    | left => exact matrix model S A start source.left rest hA hCap
    | right => exact matrix model S A start source.right rest hA hCap
  have hPos : ∀ field,∀ size ∈ GeneralPaperSegmentRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | weights => exact GeneralPaperMeasuredPlanPositive.array model S A _ source.weights hA (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
    | left => exact GeneralPaperEqualMeasuredPlanPositive.matrix model S A source.left hA
    | right => exact GeneralPaperEqualMeasuredPlanPositive.matrix model S A source.right hA
  rw [GeneralPaperSegmentRecordCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 40 (GeneralPaperSegmentRecordCursor.parser S A source)
    (GeneralPaperSegmentRecordCursor.schema model S A source) (GeneralPaperSegmentRecordCursor.child model S A source)
    hParser hPrice hPos hA start 32 GeneralPaperSegmentRecordCursor.fields rest (by decide) hCap
  simpa only [GeneralPaperSegmentRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperSegmentRecordCursor.plan,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

theorem prepared {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A) :
    (GeneralPaperPreparedRecordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1 ++ rest)).work ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum + 1) * 104 * unit model S A := by
  have hParser : Correct model S A (GeneralPaperPreparedRecordCursor.schema model S A source)
      (GeneralPaperPreparedRecordCursor.child model S A source) (GeneralPaperPreparedRecordCursor.parser S A source) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := GeneralPaperPreparedRecordCursor.field_success model S A source field start rest
    exact ⟨hv,hr,hs⟩
  have hPrice : Price model S A 72 (GeneralPaperPreparedRecordCursor.schema model S A source) (GeneralPaperPreparedRecordCursor.parser S A source) := by
    intro field start rest hCap
    cases field with
    | routes => exact raise model S A _ 40 72 _ (route_array model S A start source.routes.table rest hA hCap) (by decide)
    | segments => exact segments model S A start source.segments rest hA hCap
    | counts => exact raise model S A _ 16 72 _ (GeneralPaperMappedCursorWork.natural model S A start source.counts rest hA hCap) (by decide)
    | controls => exact raise model S A _ 16 72 _ (GeneralPaperMappedCursorWork.naturals_plan model S A start (GeneralPaperPreparedRecordCursor.controls source) rest hA hCap) (by decide)
    | budget =>
      simp only [GeneralPaperPreparedRecordCursor.schema,GeneralPaperPreparedRecordCursor.parser,
        GeneralPaperMeasuredBlockPlan.rational_data,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
      exact raise model S A _ 3 72 _ (GeneralPaperScalarCursorWork.leaf_layout model S A start (.rational source.budget) rest hA hCap) (by decide)
  have hPos : ∀ field,∀ size ∈ GeneralPaperPreparedRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | routes => exact GeneralPaperMeasuredPlanPositive.array model S A _ source.routes.table hA (fun j => GeneralPaperEqualMeasuredPlanPositive.route model S A _ hA)
    | segments => exact GeneralPaperEqualMeasuredPlanPositive.segments model S A source.segments hA
    | counts => exact GeneralPaperMeasuredPlanPositive.array model S A _ source.counts hA (fun j => GeneralPaperMeasuredPlanPositive.natural model S _)
    | controls => exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega) (fun value _ => GeneralPaperMeasuredPlanPositive.natural model S value)
    | budget => exact GeneralPaperMeasuredPlanPositive.rational model S source.budget
  rw [GeneralPaperPreparedRecordCursor.plan] at hCap
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have h := GeneralPaperRecordCursorWork.trailing model S A 72 (GeneralPaperPreparedRecordCursor.parser S A source)
    (GeneralPaperPreparedRecordCursor.schema model S A source) (GeneralPaperPreparedRecordCursor.child model S A source)
    hParser hPrice hPos hA start 64 GeneralPaperPreparedRecordCursor.fields rest (by decide) hCap
  simpa only [GeneralPaperPreparedRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperPreparedRecordCursor.plan,
    List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

end Blotto.GeneralPaperPreparedCursorWork
