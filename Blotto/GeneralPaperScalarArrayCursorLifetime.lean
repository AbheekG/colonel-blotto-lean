import Blotto.GeneralPaperScalarSourceMappingLifetime

/-! Complete actual scalar-array extraction lifetime: scalar cursor,
target traversal, returned header, saved prices and local region-read
scratch. Actual successful prefixes derive every output condition and
leave following region suffixes untouched. -/
namespace Blotto.GeneralPaperScalarArrayCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperScalarArrayFieldCursor (run targets fields)
open GeneralPaperScalarFieldCursor (cells)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def controls (S A : ℕ) (values : List Scalar) (header : Region A) (first rest : List (Region A)) : List ℕ :=
  let payload := GeneralPaperScalarFieldCursor.run S A values (first ++ rest)
  let targetWork := (targets S A (cells A first values)).2
  [S,A,payload.work,targetWork,payload.work + targetWork,GeneralPaperLastRegionSelection.price S A header,
    payload.work + targetWork + GeneralPaperLastRegionSelection.price S A header,
    (run S A values (header :: (first ++ rest))).work]

def window (S A : ℕ) (values : List Scalar) (header : Region A) (first rest : List (Region A)) : ℕ :=
  GeneralPaperScalarFieldCursorLifetime.window S A values first rest +
    GeneralPaperScalarCursorTargetLifetime.window S A (cells A first values) +
    GeneralPaperFieldDirectoryStorage.headerFoot S (fields A header (cells A first values)).header +
    GeneralPaperMeasuredLayoutStorage.regionFoot S header + GeneralPaperLastRegionSelection.price S A header +
    fields S (controls S A values header first rest) + 128 * S

theorem prefix_bound (model : RationalCostModel) (S A Q : ℕ) (values : List Scalar) (header : Region A)
    (first rest : List (Region A)) (hA : 0 < A) (hLength : first.length = values.length)
    (hCap : ∀ region ∈ first,region.stop < 2 ^ A) (hHeaderCap : header.stop < 2 ^ A)
    (hHeader : header.length = A * (64 + values.length))
    (hWork : (run S A values (header :: (first ++ rest))).work ≤ Q) :
    window S A values header first rest ≤ ((values.map encode).sum + 1) * 24 * unit model S A Q := by
  have hSome := (GeneralPaperScalarFieldCursor.on_prefix S A first rest values hLength).1
  have hWhole := hWork
  simp only [run,hSome] at hWork
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
  have hValid := GeneralPaperScalarArrayFieldCursor.header_valid A header first values hLength hHeader
  have hHeaderFoot := GeneralPaperFieldDirectoryStorage.header_bound S A (fields A header (cells A first values)).header hA hValid hHeaderCap
  change GeneralPaperFieldDirectoryStorage.headerFoot S _ ≤
    (((cells A first values).map (fun cell => cell.region.reference)).length + 1) * 384 * (S + A + 1) at hHeaderFoot
  rw [List.length_map,hCount] at hHeaderFoot
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A header hA hHeaderCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A header hA hHeaderCap
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A values header first rest) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hN := GeneralPaperScalarCursorWork.count_le_payload values
  have hCountPay := Nat.mul_le_mul_right (unit model S A Q) (Nat.add_le_add_right hN 1)
  have hHeaderUnit : 384 * (S + A + 1) ≤ unit model S A Q := by omega
  have hHeaderPay := Nat.mul_le_mul_left (values.length + 1) hHeaderUnit
  have hParent : GeneralPaperMeasuredLayoutStorage.regionFoot S header + GeneralPaperLastRegionSelection.price S A header +
      fields S (controls S A values header first rest) + 128 * S ≤ unit model S A Q := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    omega
  have hPayloadPay := Nat.mul_le_mul_left (values.map encode).sum (show 2 ≤ unit model S A Q by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ (values.map encode).sum + 1 by omega)
  unfold window
  nlinarith only [hScalar,hTarget,hHeaderFoot,hCountPay,hHeaderPay,hParent,hPayloadPay,hBase]

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 24 * unit model S A ((B + 1) * 8 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem layout_bound (model : RationalCostModel) (S A start : ℕ) (values : List Scalar) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + (A * (64 + values.length) + (values.map encode).sum) < 2 ^ A) :
    let header := GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length
    let first := (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1
    window S A values header first rest ≤ profile model S A (A * (64 + values.length) + (values.map encode).sum) := by
  dsimp only
  have hRange := GeneralPaperSequentialLayout.range model S A (start + A * (64 + values.length)) (values.map encode)
  have hWork := GeneralPaperScalarCursorWork.array_layout model S A start values rest hA hCap
  rw [GeneralPaperScalarArrayFieldCursor.layout_regions,List.cons_append] at hWork
  have h := prefix_bound model S A _ values (GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length)
    (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1 rest hA
    (by rw [GeneralPaperSequentialLayout.count,List.length_map])
    (fun region hr => (hRange region hr).2.trans_lt (by omega))
    (by change start + A * (64 + values.length) < 2 ^ A; omega) rfl hWork
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 24 (by omega)))

end Blotto.GeneralPaperScalarArrayCursorLifetime
