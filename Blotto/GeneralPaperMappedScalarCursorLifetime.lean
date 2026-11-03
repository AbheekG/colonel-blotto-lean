import Blotto.GeneralPaperScalarArrayCursorLifetime

/-! Complete mapped scalar-array directory extraction. Typed source
mapping, scalar and target cursors, the complete returned directory and
both enclosing wrapper price/control records coexist. Every source scalar
keeps its own precision; following region suffixes remain shared. -/
namespace Blotto.GeneralPaperMappedScalarCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def stream {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (header : Region A) (first rest : List (Region A)) : GeneralPaperScalarArrayFieldCursor.Result A :=
  GeneralPaperMappedScalarArrayCursor.run S A lift source (header :: (first ++ rest))

def output {α : Type*} {n : ℕ} (A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (header : Region A) (first : List (Region A)) : GeneralPaperFieldDirectory.Directory A :=
  GeneralPaperFieldDirectory.ofArray (GeneralPaperScalarArrayFieldCursor.fields A header
    (GeneralPaperScalarFieldCursor.cells A first (source.data.toList.map lift)))

def controls {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (header : Region A) (first rest : List (Region A)) : List ℕ :=
  let actual := stream S A lift source header first rest
  let mappingWork := (GeneralPaperMappedScalarArrayCursor.liftValues S A lift source.data.toList).2
  let parserWork := (GeneralPaperScalarArrayFieldCursor.run S A (source.data.toList.map lift) (header :: (first ++ rest))).work
  [S,A,mappingWork,parserWork,mappingWork+parserWork,actual.work,GeneralPaperLastRegionSelection.price S A header,
    (GeneralPaperFieldDirectoryParsers.fromArray S A actual).work]

def window {α : Type*} {n : ℕ} (S A : ℕ) (lift : α → Scalar) (source : FixedArrayTable n α)
    (header : Region A) (first rest : List (Region A)) : ℕ :=
  GeneralPaperScalarSourceMappingLifetime.window S A lift source.data.toList +
    GeneralPaperScalarArrayCursorLifetime.window S A (source.data.toList.map lift) header first rest +
    GeneralPaperFieldDirectoryStorage.directoryFoot S (output A lift source header first) +
    GeneralPaperLastRegionSelection.price S A header + fields S (controls S A lift source header first rest) + 192 * S

theorem prefix_bound {α : Type*} {n : ℕ} (model : RationalCostModel) (S A Q : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (header : Region A) (first rest : List (Region A))
    (hA : 0 < A) (hLength : first.length = (source.data.toList.map lift).length)
    (hCap : ∀ region ∈ first,region.stop < 2 ^ A) (hHeaderCap : header.stop < 2 ^ A)
    (hHeader : header.length = A * (64 + (source.data.toList.map lift).length))
    (hWork : (GeneralPaperFieldDirectoryParsers.fromArray S A (stream S A lift source header first rest)).work ≤ Q) :
    window S A lift source header first rest ≤ (((source.data.toList.map lift).map encode).sum + 1) * 48 * unit model S A Q := by
  let values := source.data.toList.map lift
  have hSome : (stream S A lift source header first rest).values = some
      (GeneralPaperScalarArrayFieldCursor.fields A header (GeneralPaperScalarFieldCursor.cells A first values)) := by
    rw [stream,GeneralPaperMappedScalarArrayCursor.run_values]
    exact (GeneralPaperScalarArrayFieldCursor.on_prefix S A header first rest values hLength).1
  have hFrom := GeneralPaperFieldDirectoryParsers.from_array_work S A (stream S A lift source header first rest) _ hSome
  change (GeneralPaperFieldDirectoryParsers.fromArray S A (stream S A lift source header first rest)).work =
    (stream S A lift source header first rest).work + GeneralPaperLastRegionSelection.price S A header + 64 * (S + A + 1) at hFrom
  have hWhole := hWork
  rw [hFrom] at hWork
  have hStream : (stream S A lift source header first rest).work =
      (GeneralPaperMappedScalarArrayCursor.liftValues S A lift source.data.toList).2 +
      (GeneralPaperScalarArrayFieldCursor.run S A values (header :: (first ++ rest))).work + 64 * (S + A + 1) := by
    simp only [stream,GeneralPaperMappedScalarArrayCursor.run,GeneralPaperMappedScalarArrayCursor.lift_data,values]
  dsimp only [values] at hStream
  have hMapping := GeneralPaperScalarSourceMappingLifetime.window_bound model S A Q lift source.data.toList (by omega)
  have hParser := GeneralPaperScalarArrayCursorLifetime.prefix_bound model S A Q values header first rest hA hLength hCap hHeaderCap hHeader (by dsimp only [values]; omega)
  have hCells := GeneralPaperScalarFieldCursorLifetime.output_cells_bound S A first values hA hLength hCap
  have hHeaderValid := GeneralPaperScalarArrayFieldCursor.header_valid A header first values hLength hHeader
  have hHeaderFoot := GeneralPaperFieldDirectoryStorage.header_bound S A
    (GeneralPaperScalarArrayFieldCursor.fields A header (GeneralPaperScalarFieldCursor.cells A first values)).header hA hHeaderValid hHeaderCap
  have hCellCount := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A first values hLength)
  simp only [List.length_map] at hCellCount
  change GeneralPaperFieldDirectoryStorage.headerFoot S _ ≤
    (((GeneralPaperScalarFieldCursor.cells A first values).map (fun cell => cell.region.reference)).length + 1) * 384 * (S + A + 1) at hHeaderFoot
  rw [List.length_map,hCellCount] at hHeaderFoot
  dsimp only [GeneralPaperScalarArrayFieldCursor.fields] at hHeaderFoot
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A header hA hHeaderCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A header hA hHeaderCap
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A lift source header first rest) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hN := GeneralPaperScalarCursorWork.count_le_payload values
  have hUnit := unit_bounds model S A Q
  have hMeta : 192 * (S + A + 1) + 2 * S ≤ unit model S A Q := by omega
  have hMetaPay := Nat.mul_le_mul_left values.length hMeta
  have hHeaderMeta : 384 * (S + A + 1) ≤ unit model S A Q := by omega
  have hHeaderPay := Nat.mul_le_mul_left (values.length + 1) hHeaderMeta
  have hCountPay := Nat.mul_le_mul_right (unit model S A Q) (Nat.add_le_add_right hN 1)
  have hPayloadPay := Nat.mul_le_mul_left (values.map encode).sum (show 1 ≤ unit model S A Q by omega)
  have hDirectory : GeneralPaperFieldDirectoryStorage.directoryFoot S (output A lift source header first) ≤
      ((values.map encode).sum + 1) * 4 * unit model S A Q := by
    dsimp only [output,GeneralPaperFieldDirectory.ofArray,GeneralPaperScalarArrayFieldCursor.fields,
      GeneralPaperFieldDirectoryStorage.directoryFoot]
    simp only [listFootprint,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    change GeneralPaperMeasuredLayoutStorage.regionFoot S header +
      (GeneralPaperFieldDirectoryStorage.headerFoot S ⟨header,64,(GeneralPaperScalarFieldCursor.cells A first values).map (fun cell => cell.region.reference)⟩ + 0 + 1 * (2 * S) + 32 * S) +
      (((GeneralPaperScalarFieldCursor.cells A first values).map (GeneralPaperFieldDirectoryStorage.cellFoot S)).sum +
      (GeneralPaperScalarFieldCursor.cells A first values).length * (2 * S) + 32 * S) + 64 * S ≤ _
    change listFootprint S (GeneralPaperFieldDirectoryStorage.cellFoot S) (GeneralPaperScalarFieldCursor.cells A first values) ≤ _ at hCells
    dsimp only [listFootprint] at hCells
    rw [hCellCount] at hCells ⊢
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    nlinarith only [hCells,hHeaderFoot,hRegion,hMetaPay,hHeaderPay,hCountPay,hPayloadPay,hUnit]
  have hParent : GeneralPaperLastRegionSelection.price S A header + fields S (controls S A lift source header first rest) + 192 * S ≤ unit model S A Q := by omega
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ (values.map encode).sum + 1 by omega)
  have hMapSum : (source.data.toList.map (fun value => encode (lift value))).sum = (values.map encode).sum := by
    simp only [values,List.map_map,Function.comp_def]
  rw [hMapSum] at hMapping
  unfold window
  change _ ≤ ((values.map encode).sum + 1) * 48 * unit model S A Q
  nlinarith only [hMapping,hParser,hDirectory,hParent,hBase]

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 48 * unit model S A ((B + 1) * 16 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem layout_bound {α : Type*} {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (lift : α → Scalar)
    (source : FixedArrayTable n α) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (A * (64 + (source.data.toList.map lift).length) + ((source.data.toList.map lift).map encode).sum) < 2 ^ A) :
    let values := source.data.toList.map lift
    window S A lift source (GeneralPaperScalarArrayFieldCursor.layoutHeader A start values.length)
      (GeneralPaperSequentialLayout.run model S A (start + A * (64 + values.length)) (values.map encode)).1 rest ≤
      profile model S A (A * (64 + values.length) + (values.map encode).sum) := by
  dsimp only
  have hRange := GeneralPaperSequentialLayout.range model S A (start + A * (64 + (source.data.toList.map lift).length))
    ((source.data.toList.map lift).map encode)
  have hWork := GeneralPaperMappedCursorWork.mapped_array model S A start lift source rest hA hCap
  rw [GeneralPaperScalarArrayFieldCursor.layout_regions,List.cons_append] at hWork
  have h := prefix_bound model S A _ lift source _ _ rest hA
    (by rw [GeneralPaperSequentialLayout.count,List.length_map])
    (fun region hr => (hRange region hr).2.trans_lt (by omega))
    (by change start + A * (64 + (source.data.toList.map lift).length) < 2 ^ A; omega) rfl hWork
  exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right 48 (by omega)))

end Blotto.GeneralPaperMappedScalarCursorLifetime
