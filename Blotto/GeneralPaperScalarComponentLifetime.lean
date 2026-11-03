import Blotto.GeneralPaperScalarRecordCursorLifetime

/-! Actual scalar leaves and natural-control lists, including typed
source mapping and complete enclosing saved prices. Original-budget scalar
width occurs additively in the single leaf payload. -/
namespace Blotto.GeneralPaperScalarComponentLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem lift_same {α : Type*} (S A : ℕ) (lift : α → Scalar) (values : List α) :
    GeneralPaperScalarRecordComponents.lift S A lift values = GeneralPaperMappedScalarArrayCursor.liftValues S A lift values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [GeneralPaperScalarRecordComponents.lift,GeneralPaperMappedScalarArrayCursor.liftValues,ih]

def leafWindow (model : RationalCostModel) (S A start : ℕ) (value : Scalar) (rest : List (Region A)) : ℕ :=
  GeneralPaperScalarFieldCursorLifetime.window S A [value]
      (GeneralPaperSequentialLayout.run model S A start [encode value]).1 rest +
    GeneralPaperFieldDirectoryStorage.directoryFoot S (GeneralPaperScalarRecordComponents.leafExpected A start value) + encode value +
    fields S [S,A,(GeneralPaperScalarRecordComponents.leafRun S A value
      ((GeneralPaperSequentialLayout.run model S A start [encode value]).1 ++ rest)).work] + 128 * S

theorem leaf_bound (model : RationalCostModel) (S A start Q : ℕ) (value : Scalar) (rest : List (Region A))
    (hA : 0 < A) (hCap : start + encode value < 2 ^ A)
    (hWork : (GeneralPaperScalarRecordComponents.leafRun S A value
      ((GeneralPaperSequentialLayout.run model S A start [encode value]).1 ++ rest)).work ≤ Q) :
    leafWindow model S A start value rest ≤ (encode value + 1) * 16 * unit model S A Q := by
  let regions := (GeneralPaperSequentialLayout.run model S A start [encode value]).1
  let total := (GeneralPaperScalarRecordComponents.leafRun S A value (regions ++ rest)).work
  change total ≤ Q at hWork
  have hCount : regions.length = [value].length := by dsimp only [regions]; rw [GeneralPaperSequentialLayout.count]; rfl
  have hRange := GeneralPaperSequentialLayout.range model S A start [encode value]
  have hScalarPrice : (GeneralPaperScalarFieldCursor.run S A [value] (regions ++ rest)).work = total := by
    simp only [regions,total,GeneralPaperSequentialLayout.run,GeneralPaperStoredWordEncoding.word_data,List.singleton_append,
      GeneralPaperScalarFieldCursor.run,GeneralPaperScalarRecordComponents.leafRun]
    ring
  have hScalar := GeneralPaperScalarFieldCursorLifetime.window_bound model S A Q regions rest [value] hA hCount
    (fun region hr => (hRange region hr).2.trans_lt (by simpa only [List.sum_cons,List.sum_nil,Nat.add_zero] using hCap))
    (by rw [hScalarPrice]; exact hWork)
  have hPositive : GeneralPaperMeasuredPlanPositive.Positive (⟨[encode value],0⟩ : GeneralPaperMeasuredBlockPlan.Plan) := by
    intro size hs
    have he := List.mem_singleton.mp hs
    subst size
    have h := GeneralPaperScalarCursorWork.count_le_payload [value]
    simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at h
    omega
  have hDirectory := GeneralPaperFieldDirectoryStorage.directory_bound model S A start
    (⟨[encode value],0⟩ : GeneralPaperMeasuredBlockPlan.Plan) (GeneralPaperScalarRecordComponents.leafExpected A start value)
    (GeneralPaperScalarRecordComponents.leaf_success model S A start value rest).2.2.1 hPositive hA
    (by simpa only [List.sum_cons,List.sum_nil,Nat.add_zero] using hCap)
  change GeneralPaperFieldDirectoryStorage.directoryFoot S _ ≤ (encode value + 1) * 2048 * (S + A + 1) at hDirectory
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,total] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hDirPay := Nat.mul_le_mul_left (encode value + 1) (show 2048 * (S + A + 1) ≤ unit model S A Q by omega)
  have hPayload := Nat.mul_le_mul_left (encode value) (show 1 ≤ unit model S A Q by omega)
  have hParent : fields S [S,A,total] + 128 * S ≤ unit model S A Q := by omega
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ encode value + 1 by omega)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at hScalar
  unfold leafWindow
  nlinarith only [hScalar,hDirectory,hDirPay,hPayload,hParent,hBase]

def naturalControls (S A start : ℕ) (model : RationalCostModel) (values : List ℕ) (rest : List (Region A)) : List ℕ :=
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values)).1 ++ rest
  let mappingWork := (GeneralPaperScalarRecordComponents.lift S A Scalar.natural values).2
  let parserWork := (GeneralPaperScalarRecordComponents.listRun S A 32 (values.map Scalar.natural) regions).work
  [S,A,mappingWork,parserWork,mappingWork + parserWork,(GeneralPaperScalarRecordComponents.naturals S A values regions).work]

def naturalWindow (model : RationalCostModel) (S A start : ℕ) (values : List ℕ) (rest : List (Region A)) : ℕ :=
  GeneralPaperScalarSourceMappingLifetime.window S A Scalar.natural values +
    GeneralPaperScalarRecordCursorLifetime.frontWindow model S A start 32 1 (values.map Scalar.natural) rest +
    fields S (naturalControls S A start model values rest) + 128 * S

theorem natural_bound (model : RationalCostModel) (S A start Q : ℕ) (values : List ℕ) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperScalarRecordComponents.naturals S A values
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values)).1 ++ rest)).work ≤ Q) :
    naturalWindow model S A start values rest ≤
      ((GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values).sizes.sum + 1) * 48 * unit model S A Q := by
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
    (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) values)).1 ++ rest
  change (GeneralPaperScalarRecordComponents.naturals S A values regions).work ≤ Q at hWork
  have hTotal : (GeneralPaperScalarRecordComponents.naturals S A values regions).work =
      (GeneralPaperMappedScalarArrayCursor.liftValues S A Scalar.natural values).2 +
      (GeneralPaperScalarRecordComponents.listRun S A 32 (values.map Scalar.natural) regions).work + 64 * (S + A + 1) := by
    simp only [GeneralPaperScalarRecordComponents.naturals,lift_same,GeneralPaperMappedScalarArrayCursor.lift_data]
  have hMapping := GeneralPaperScalarSourceMappingLifetime.window_bound model S A Q Scalar.natural values (by omega)
  have hMapSum : (values.map (fun value => encode (Scalar.natural value))).sum = ((values.map Scalar.natural).map encode).sum := by
    simp only [List.map_map,Function.comp_def]
  rw [hMapSum] at hMapping
  have hParsed : (GeneralPaperScalarRecordComponents.listRun S A 32 (values.map Scalar.natural) regions).work ≤ Q := by omega
  dsimp only [regions,GeneralPaperMeasuredBlockLayout.run] at hParsed
  rw [GeneralPaperScalarRecordComponents.natural_plan] at hParsed
  rw [GeneralPaperScalarRecordComponents.natural_plan,List.sum_cons] at hCap ⊢
  have hParser := GeneralPaperScalarRecordCursorLifetime.front_bound model S A start 32 1 Q (values.map Scalar.natural) rest hA (by decide) hCap hParsed
  have hRawTotal := hTotal
  have hRawWork := hWork
  dsimp only [regions] at hRawTotal hRawWork
  have hFields := fields_bound S (natBits (cap S A Q)) (naturalControls S A start model values rest) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [naturalControls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [lift_same] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S (naturalControls S A start model values rest) + 128 * S ≤ unit model S A Q := by omega
  have hMass := Nat.mul_le_mul_right (8 * unit model S A Q)
    (show ((values.map Scalar.natural).map encode).sum + 1 ≤
      A * (1 * (values.map Scalar.natural).length + 32) + ((values.map Scalar.natural).map encode).sum + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ A * (1 * (values.map Scalar.natural).length + 32) + ((values.map Scalar.natural).map encode).sum + 1 by omega)
  unfold naturalWindow
  nlinarith only [hMapping,hParser,hParent,hMass,hBase]

end Blotto.GeneralPaperScalarComponentLifetime
