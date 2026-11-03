import Blotto.GeneralPaperSegmentCursorLifetime

/-! Common complete scalar-record assembly window. The executing front
and trailing parsers supply their actual scalar suffix and total price;
no extra parser or target traversal is inserted. -/
namespace Blotto.GeneralPaperScalarRecordAssemblyLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperScalarFieldCursor (cells)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def controls (S A payloadWork targetWork readWork totalWork : ℕ) : List ℕ :=
  [S,A,payloadWork,targetWork,payloadWork + targetWork,readWork,payloadWork + targetWork + readWork,totalWork]

def window (S A fixed : ℕ) (values : List Scalar) (header : Region A) (first rest : List (Region A)) (totalWork : ℕ) : ℕ :=
  GeneralPaperScalarFieldCursorLifetime.window S A values first rest +
    GeneralPaperScalarCursorTargetLifetime.window S A (cells A first values) +
    GeneralPaperFieldDirectoryStorage.directoryFoot S (GeneralPaperScalarRecordComponents.compose fixed header (cells A first values)) +
    GeneralPaperMeasuredLayoutStorage.regionFoot S header + GeneralPaperLastRegionSelection.price S A header + natBits fixed +
    fields S (controls S A (GeneralPaperScalarFieldCursor.run S A values (first ++ rest)).work
      (GeneralPaperScalarArrayFieldCursor.targets S A (cells A first values)).2
      (GeneralPaperLastRegionSelection.price S A header) totalWork) + 128 * S

theorem window_bound (model : RationalCostModel) (S A fixed Q : ℕ) (values : List Scalar) (header : Region A)
    (first rest : List (Region A)) (totalWork : ℕ) (hA : 0 < A) (hLength : first.length = values.length)
    (hCap : ∀ region ∈ first,region.stop < 2 ^ A) (hHeaderCap : header.stop < 2 ^ A)
    (hHeader : A * (fixed + values.length) ≤ header.length) (hTotal : totalWork ≤ Q)
    (hPrices : (GeneralPaperScalarFieldCursor.run S A values (first ++ rest)).work +
      (GeneralPaperScalarArrayFieldCursor.targets S A (cells A first values)).2 +
      GeneralPaperLastRegionSelection.price S A header ≤ totalWork) :
    window S A fixed values header first rest totalWork ≤ ((values.map encode).sum + 1) * 32 * unit model S A Q := by
  have hScalar := GeneralPaperScalarFieldCursorLifetime.window_bound model S A Q first rest values hA hLength hCap (by omega)
  have hRegions := GeneralPaperScalarFieldCursor.cells_regions A first values hLength
  have hValues := GeneralPaperScalarFieldCursor.cells_values A first values hLength
  have hCellsCap : ∀ cell ∈ cells A first values,cell.region.stop < 2 ^ A := by
    intro cell hc
    apply hCap cell.region
    rw [← hRegions]
    exact List.mem_map.mpr ⟨cell,hc,rfl⟩
  have hTarget := GeneralPaperScalarCursorTargetLifetime.window_bound model S A Q (cells A first values) hA hCellsCap (by omega)
  have hCount := congrArg List.length hValues
  simp only [List.length_map] at hCount
  have hPayload := congrArg (fun xs => (xs.map encode).sum) hValues
  simp only [List.map_map,Function.comp_def] at hPayload
  rw [hCount,hPayload] at hTarget
  let record : GeneralPaperReferenceRegionSlots.Header A := ⟨header,fixed,(cells A first values).map (fun cell => cell.region.reference)⟩
  have hValid : GeneralPaperReferenceRegionSlots.Valid record := by
    simpa only [record,GeneralPaperReferenceRegionSlots.Valid,List.length_map,hCount] using hHeader
  have hHead := GeneralPaperFieldDirectoryStorage.header_bound S A record hA hValid hHeaderCap
  change GeneralPaperFieldDirectoryStorage.headerFoot S record ≤
    (((cells A first values).map (fun cell => cell.region.reference)).length + 1) * 384 * (S + A + 1) at hHead
  rw [List.length_map,hCount] at hHead
  obtain ⟨_,_,hFixed,_⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths record hA hValid hHeaderCap
  have hFixedBits : natBits fixed ≤ A + 1 := by change 1 + binaryWordWidth fixed ≤ A + 1; change binaryWordWidth fixed ≤ A at hFixed; omega
  have hCells := GeneralPaperScalarFieldCursorLifetime.output_cells_bound S A first values hA hLength hCap
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A header hA hHeaderCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A header hA hHeaderCap
  have hFields := fields_bound S (natBits (cap S A Q))
    (controls S A (GeneralPaperScalarFieldCursor.run S A values (first ++ rest)).work
      (GeneralPaperScalarArrayFieldCursor.targets S A (cells A first values)).2
      (GeneralPaperLastRegionSelection.price S A header) totalWork) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hN := GeneralPaperScalarCursorWork.count_le_payload values
  have hUnit := unit_bounds model S A Q
  have hMetaPay := Nat.mul_le_mul_left values.length (show 192 * (S + A + 1) + 2 * S ≤ unit model S A Q by omega)
  have hHeaderPay := Nat.mul_le_mul_left (values.length + 1) (show 384 * (S + A + 1) ≤ unit model S A Q by omega)
  have hCountPay := Nat.mul_le_mul_right (unit model S A Q) (Nat.add_le_add_right hN 1)
  have hPayloadPay := Nat.mul_le_mul_left (values.map encode).sum (show 3 ≤ unit model S A Q by omega)
  have hDirectory : GeneralPaperFieldDirectoryStorage.directoryFoot S
      (GeneralPaperScalarRecordComponents.compose fixed header (cells A first values)) ≤
      ((values.map encode).sum + 1) * 4 * unit model S A Q := by
    dsimp only [GeneralPaperScalarRecordComponents.compose,GeneralPaperFieldDirectoryStorage.directoryFoot]
    change GeneralPaperMeasuredLayoutStorage.regionFoot S header +
      (GeneralPaperFieldDirectoryStorage.headerFoot S record + 0 + 1 * (2 * S) + 32 * S) +
      listFootprint S (GeneralPaperFieldDirectoryStorage.cellFoot S) (cells A first values) + 64 * S ≤ _
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    nlinarith only [hCells,hHead,hRegion,hMetaPay,hHeaderPay,hCountPay,hPayloadPay,hUnit]
  have hParent : GeneralPaperMeasuredLayoutStorage.regionFoot S header + GeneralPaperLastRegionSelection.price S A header + natBits fixed +
      fields S (controls S A (GeneralPaperScalarFieldCursor.run S A values (first ++ rest)).work
        (GeneralPaperScalarArrayFieldCursor.targets S A (cells A first values)).2
        (GeneralPaperLastRegionSelection.price S A header) totalWork) + 128 * S ≤ unit model S A Q := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    omega
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ (values.map encode).sum + 1 by omega)
  unfold window
  nlinarith only [hScalar,hTarget,hDirectory,hParent,hPayloadPay,hCountPay,hBase]

end Blotto.GeneralPaperScalarRecordAssemblyLifetime
