import Blotto.GeneralPaperPreparedCursorLifetime

/-! Complete typed bit-list extraction lifetime. Actual stored bits are
mapped and consumed once, retaining the front scalar-record and wrapper
prices without re-encoding an integer. -/
namespace Blotto.GeneralPaperBooleanBitCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def controls (S A start : ℕ) (model : RationalCostModel) (values : List Bool) (rest : List (Region A)) : List ℕ :=
  let regions := (GeneralPaperSequentialLayout.run model S A start
    (GeneralPaperBooleanWordCursor.bitsSchema model S A values)).1 ++ rest
  let mappingWork := (GeneralPaperScalarRecordComponents.lift S A Scalar.bit values).2
  let parserWork := (GeneralPaperScalarRecordComponents.listRun S A 32 (values.map Scalar.bit) regions).work
  [S,A,mappingWork,parserWork,mappingWork + parserWork,(GeneralPaperBooleanWordCursor.bitsRun S A values regions).work]

def window (model : RationalCostModel) (S A start : ℕ) (values : List Bool) (rest : List (Region A)) : ℕ :=
  GeneralPaperScalarSourceMappingLifetime.window S A Scalar.bit values +
    GeneralPaperScalarRecordCursorLifetime.frontWindow model S A start 32 2 (values.map Scalar.bit) rest +
    fields S (controls S A start model values rest) + 128 * S

theorem window_bound (model : RationalCostModel) (S A start Q : ℕ) (values : List Bool) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperBooleanWordCursor.bitsSchema model S A values).sum < 2 ^ A)
    (hWork : (GeneralPaperBooleanWordCursor.bitsRun S A values
      ((GeneralPaperSequentialLayout.run model S A start
        (GeneralPaperBooleanWordCursor.bitsSchema model S A values)).1 ++ rest)).work ≤ Q) :
    window model S A start values rest ≤
      ((GeneralPaperBooleanWordCursor.bitsSchema model S A values).sum + 1) * 48 * unit model S A Q := by
  let regions := (GeneralPaperSequentialLayout.run model S A start
    (GeneralPaperBooleanWordCursor.bitsSchema model S A values)).1 ++ rest
  change (GeneralPaperBooleanWordCursor.bitsRun S A values regions).work ≤ Q at hWork
  have hTotal : (GeneralPaperBooleanWordCursor.bitsRun S A values regions).work =
      (GeneralPaperMappedScalarArrayCursor.liftValues S A Scalar.bit values).2 +
      (GeneralPaperScalarRecordComponents.listRun S A 32 (values.map Scalar.bit) regions).work + 64 * (S + A + 1) := by
    simp only [GeneralPaperBooleanWordCursor.bitsRun,GeneralPaperScalarComponentLifetime.lift_same,GeneralPaperMappedScalarArrayCursor.lift_data]
  have hMapping := GeneralPaperScalarSourceMappingLifetime.window_bound model S A Q Scalar.bit values (by omega)
  have hMapSum : (values.map (fun value => encode (Scalar.bit value))).sum = ((values.map Scalar.bit).map encode).sum := by
    simp only [List.map_map,Function.comp_def]
  rw [hMapSum] at hMapping
  have hParsed : (GeneralPaperScalarRecordComponents.listRun S A 32 (values.map Scalar.bit) regions).work ≤ Q := by omega
  dsimp only [regions] at hParsed
  rw [GeneralPaperBooleanWordCursor.bits_plan] at hParsed
  rw [GeneralPaperBooleanWordCursor.bits_plan,List.sum_cons] at hCap ⊢
  have hParser := GeneralPaperScalarRecordCursorLifetime.front_bound model S A start 32 2 Q (values.map Scalar.bit) rest hA (by decide) hCap hParsed
  have hRawTotal := hTotal
  have hRawWork := hWork
  dsimp only [regions] at hRawTotal hRawWork
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A start model values rest) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [GeneralPaperScalarComponentLifetime.lift_same] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S (controls S A start model values rest) + 128 * S ≤ unit model S A Q := by omega
  have hMass := Nat.mul_le_mul_right (8 * unit model S A Q)
    (show ((values.map Scalar.bit).map encode).sum + 1 ≤
      A * (2 * (values.map Scalar.bit).length + 32) + ((values.map Scalar.bit).map encode).sum + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ A * (2 * (values.map Scalar.bit).length + 32) + ((values.map Scalar.bit).map encode).sum + 1 by omega)
  unfold window
  nlinarith only [hMapping,hParser,hParent,hMass,hBase]

end Blotto.GeneralPaperBooleanBitCursorLifetime
