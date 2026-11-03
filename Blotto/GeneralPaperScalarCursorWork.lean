import Blotto.GeneralPaperDirectoryCopyWork

/-! Complete scalar-region extraction and front-header construction work.
Every scalar is charged by its own encoding, and each source/region is
visited once. An arbitrary following region suffix is left uncharged. -/
namespace Blotto.GeneralPaperScalarCursorWork
open GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperMeasuredPlanWorkAlgebra GeneralPaperDirectoryCopyWork
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem count_le_payload (values : List Scalar) : values.length ≤ (values.map encode).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have h := positive value
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem on_prefix (model : RationalCostModel) (S A : ℕ) (regions rest : List (Region A)) (values : List Scalar)
    (hLength : regions.length = values.length)
    (hRegion : ∀ region ∈ regions,GeneralPaperLastRegionSelection.price S A region ≤ unit model S A) :
    (GeneralPaperScalarFieldCursor.run S A values (regions ++ rest)).work ≤
      (values.map encode).sum + (2 * values.length + 1) * unit model S A := by
  have hSum := GeneralPaperEncodedScalarStorage.sum_bound (GeneralPaperLastRegionSelection.price S A) (unit model S A) regions hRegion
  rw [hLength] at hSum
  have hMeta := metadata model S A
  have hStep := Nat.mul_le_mul_left values.length (show 64 * (S + A + 1) ≤ unit model S A by omega)
  rw [GeneralPaperScalarFieldCursor.work_on_prefix S A regions rest values hLength]
  nlinarith only [hSum,hStep,hMeta.2.1]

theorem layout (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (values.map encode).sum < 2 ^ A) :
    (GeneralPaperScalarFieldCursor.run S A values
      ((GeneralPaperSequentialLayout.run model S A start (values.map encode)).1 ++ rest)).work ≤
      ((values.map encode).sum + 1) * 4 * unit model S A := by
  have hLength : (GeneralPaperSequentialLayout.run model S A start (values.map encode)).1.length = values.length := by
    rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hRegions := layout_region_work model S A start (⟨values.map encode,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) hA hCap
  have h := on_prefix model S A _ rest values hLength hRegions
  have hCount := count_le_payload values
  have hMeta := metadata model S A
  have hPay := Nat.mul_le_mul_left (values.map encode).sum hMeta.1
  have hCountPrice := Nat.mul_le_mul_right (unit model S A) (show 2 * values.length + 1 ≤ 2 * (values.map encode).sum + 1 by omega)
  nlinarith only [h,hPay,hCountPrice,Nat.zero_le ((values.map encode).sum * unit model S A)]

theorem targets (model : RationalCostModel) (S A : ℕ) (cells : List (Cell A)) :
    (GeneralPaperScalarArrayFieldCursor.targets S A cells).2 ≤ (cells.length + 1) * unit model S A := by
  rw [GeneralPaperScalarArrayFieldCursor.targets_work]
  have h0 : A + 64 * (S + A + 1) ≤ unit model S A := by unfold unit; omega
  have h1 := Nat.mul_le_mul_left cells.length h0
  have hMeta := metadata model S A
  nlinarith only [h1,hMeta.2.1]

theorem array_on_prefix (model : RationalCostModel) (S A : ℕ) (header : Region A)
    (regions rest : List (Region A)) (values : List Scalar) (hLength : regions.length = values.length)
    (hRegion : ∀ region ∈ regions,GeneralPaperLastRegionSelection.price S A region ≤ unit model S A)
    (hHeader : GeneralPaperLastRegionSelection.price S A header ≤ unit model S A) :
    (GeneralPaperScalarArrayFieldCursor.run S A values (header :: (regions ++ rest))).work ≤
      (values.map encode).sum + (3 * values.length + 5) * unit model S A := by
  have hPayload := on_prefix model S A regions rest values hLength hRegion
  have hValues := (GeneralPaperScalarFieldCursor.on_prefix S A regions rest values hLength).1
  have hCount := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at hCount
  have hTargets := targets model S A (GeneralPaperScalarFieldCursor.cells A regions values)
  rw [hCount] at hTargets
  have hMeta := metadata model S A
  simp only [GeneralPaperScalarArrayFieldCursor.run,hValues]
  nlinarith only [hPayload,hTargets,hHeader,hMeta.2.1,Nat.zero_le (unit model S A)]

theorem array_layout (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (A * (64 + values.length) + (values.map encode).sum) < 2 ^ A) :
    (GeneralPaperScalarArrayFieldCursor.run S A values
      ((GeneralPaperSequentialLayout.run model S A start (A * (64 + values.length) :: values.map encode)).1 ++ rest)).work ≤
      (A * (64 + values.length) + (values.map encode).sum + 1) * 8 * unit model S A := by
  let next := start + A * (64 + values.length)
  have hLength : (GeneralPaperSequentialLayout.run model S A next (values.map encode)).1.length = values.length := by
    rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hRegions := layout_region_work model S A next (⟨values.map encode,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) hA (by dsimp only [next]; omega)
  have hHeader := region_work model S A (GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length) hA
    (by change start + A * (64 + values.length) < 2 ^ A; omega)
  have h := array_on_prefix model S A (GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length)
    (GeneralPaperSequentialLayout.run model S A next (values.map encode)).1 rest values hLength hRegions hHeader
  rw [GeneralPaperScalarArrayFieldCursor.layout_regions,List.cons_append]
  have hCount := count_le_payload values
  have hMeta := metadata model S A
  have hPay := Nat.mul_le_mul_left (values.map encode).sum hMeta.1
  have hPrice := Nat.mul_le_mul_right (unit model S A)
    (show 3 * values.length + 5 ≤ 7 * (A * (64 + values.length) + (values.map encode).sum + 1) by omega)
  change _ ≤ _ at h
  nlinarith only [h,hPay,hPrice,Nat.zero_le ((A * (64 + values.length)) * unit model S A)]

theorem list_layout (model : RationalCostModel) (S A start fixed stride : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (A * (stride * values.length + fixed) + (values.map encode).sum) < 2 ^ A) :
    (GeneralPaperScalarRecordComponents.listRun S A fixed values
      ((GeneralPaperSequentialLayout.run model S A start (A * (stride * values.length + fixed) :: values.map encode)).1 ++ rest)).work ≤
      (A * (stride * values.length + fixed) + (values.map encode).sum + 1) * 8 * unit model S A := by
  let header := GeneralPaperScalarRecordComponents.listHeader A start fixed stride values.length
  let next := start + A * (stride * values.length + fixed)
  let regions := (GeneralPaperSequentialLayout.run model S A next (values.map encode)).1
  have hLength : regions.length = values.length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count,List.length_map]
  have hRegions := layout_region_work model S A next (⟨values.map encode,0⟩ : GeneralPaperMeasuredBlockPlan.Plan) hA (by dsimp only [next]; omega)
  have hHeader := region_work model S A header hA (by change start + A * (stride * values.length + fixed) < 2 ^ A; omega)
  have hPayload := on_prefix model S A regions rest values hLength hRegions
  have hValues := (GeneralPaperScalarFieldCursor.on_prefix S A regions rest values hLength).1
  have hCount := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A regions values hLength)
  simp only [List.length_map] at hCount
  have hTargets := targets model S A (GeneralPaperScalarFieldCursor.cells A regions values)
  rw [hCount] at hTargets
  have hCountPayload := count_le_payload values
  have hMeta := metadata model S A
  have hPay := Nat.mul_le_mul_left (values.map encode).sum hMeta.1
  have hPrice := Nat.mul_le_mul_right (unit model S A)
    (show 3 * values.length + 5 ≤ 7 * (A * (stride * values.length + fixed) + (values.map encode).sum + 1) by omega)
  have hStream : (GeneralPaperSequentialLayout.run model S A start
      (A * (stride * values.length + fixed) :: values.map encode)).1 = header :: regions := by
    simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,header,regions,next,GeneralPaperScalarRecordComponents.listHeader]
  rw [hStream,List.cons_append]
  simp only [GeneralPaperScalarRecordComponents.listRun,hValues]
  nlinarith only [hPayload,hTargets,hHeader,hPay,hPrice,hMeta.2.1,
    Nat.zero_le ((A * (stride * values.length + fixed)) * unit model S A)]

theorem leaf_layout (model : RationalCostModel) (S A start : ℕ) (value : Scalar) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + encode value < 2 ^ A) :
    (GeneralPaperScalarRecordComponents.leafRun S A value
      ((GeneralPaperSequentialLayout.run model S A start [encode value]).1 ++ rest)).work ≤
      (encode value + 1) * 3 * unit model S A := by
  have hRegion := region_work model S A
    (⟨start,encode value,FixedBinaryWord.ofNat A start⟩ : Region A) hA hCap
  have hMeta := metadata model S A
  have hPay := Nat.mul_le_mul_left (encode value) hMeta.1
  simp only [GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,List.singleton_append,GeneralPaperScalarRecordComponents.leafRun]
  nlinarith only [hRegion,hMeta.2.1,hPay,Nat.zero_le (encode value * unit model S A)]

end Blotto.GeneralPaperScalarCursorWork
