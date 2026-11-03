import Blotto.BinaryPRGStoredDimensionFrame
import Blotto.BinaryPRGHeaderFrame
import Blotto.BinaryPRGOutputRun

/-! The complete native raw request uses the stored Boolean dimension/header
and countdown row reader. Original request fields, suffixes, output frames,
rejection and readback/hard-budget scopes remain exact. Incoming length derives
the joined recorded frame/promise/numerical ledger. Precision/seed/control,
small scalar and physical/model/whole-space work remain separate. -/

namespace Blotto.BinaryPRGStoredDimensionRequest
open BinaryRationalNormalization BinaryPRGPreparation

structure Request (n : ℕ) where
  request : BinaryPRGRequest.Request n
  header : BinaryPRGHeaderFrame.Header n

structure Ledger where
  frame : BinaryPRGStoredDimensionFrame.Ledger
  preparation : BinaryPRGMeasuredPreparation.Ledger
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.frame.recorded + ledger.preparation.recorded

def read (bits : List Bool) : Option ((Σ n, Request n) × List Bool) × Ledger :=
  let game := BinaryPRGStoredDimensionFrame.read bits
  match game.1 with
  | none => (none,⟨game.2,⟨0,0⟩⟩)
  | some parsed =>
      let prepared := BinaryPRGMeasuredPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical
      let request := prepared.1.bind (fun checked => (BinaryAccuracyWords.read parsed.2).map (fun accuracy =>
        (⟨parsed.1.1,⟨⟨checked.val,checked.property,accuracy.1,accuracy.1.precision,rfl⟩,parsed.1.2.header⟩⟩,accuracy.2)))
      (request,⟨game.2,prepared.2⟩)

def forget (parsed : (Σ n, Request n) × List Bool) : (Σ n, BinaryPRGRequest.Request n) × List Bool :=
  (⟨parsed.1.1,parsed.1.2.request⟩,parsed.2)

theorem read_state (bits : List Bool) : (read bits).1.map forget = BinaryPRGRequest.read bits := by
  have hg := BinaryPRGHeaderFrame.read_state bits
  have hv := BinaryPRGStoredDimensionFrame.read_state bits
  cases h : (BinaryPRGStoredDimensionFrame.read bits).1 with
  | none =>
      rw [h] at hv
      rw [← hv,Option.map_none] at hg
      simp only [read,h,Option.map_none,BinaryPRGRequest.read,BinaryPRGFrame.readChecked,← hg,Option.bind_none]
  | some parsed =>
      rw [h] at hv
      rw [← hv,Option.map_some] at hg
      simp only [read,h,BinaryPRGRequest.read,BinaryPRGFrame.readChecked,← hg,Option.bind_some,
        BinaryPRGMeasuredPreparation.prepareChecked_state,Option.map_bind,Option.bind_map]
      apply congrArg (Option.bind (BinaryPRGPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical))
      funext checked
      simp only [Option.map_map,Function.comp_def,forget,BinaryPRGHeaderFrame.forget]

theorem read_ledger_frame (bits : List Bool) : (read bits).2.frame = (BinaryPRGStoredDimensionFrame.read bits).2 := by
  unfold read
  dsimp only
  split <;> rfl

theorem read_ledger_bound (bits : List Bool) :
    (read bits).2.recorded ≤ (BinaryPRGStoredDimensionFrame.read bits).2.recorded +
      match (BinaryPRGStoredDimensionFrame.read bits).1 with
      | none => 0
      | some parsed => BinaryPRGMeasuredPreparation.bound parsed.1.2.game.input := by
  unfold read
  dsimp only
  split
  · exact Nat.le_refl _
  · rename_i parsed hp
    exact Nat.add_le_add_left (BinaryPRGMeasuredPreparation.prepareChecked_bound parsed.1.2.game.input parsed.1.2.game.canonical) _

theorem read_frame_bound (bits : List Bool) : (read bits).2.frame.recorded ≤ BinaryPRGStoredDimensionFrame.bound bits.length := by
  rw [read_ledger_frame]
  exact BinaryPRGStoredDimensionFrame.read_bound bits

theorem read_recorded_bound (bits : List Bool) :
    (read bits).2.recorded ≤ BinaryPRGStoredDimensionFrame.bound bits.length +
      match (BinaryPRGStoredDimensionFrame.read bits).1 with
      | none => 0
      | some parsed => BinaryPRGMeasuredPreparation.bound parsed.1.2.game.input := by
  have hr := read_ledger_bound bits
  have hf := BinaryPRGStoredDimensionFrame.read_bound bits
  exact hr.trans (Nat.add_le_add_right hf _)

def output {n : ℕ} (prepared : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n prepared.request.precision) → Bool) : List Bool × BinaryPRGOutputRun.Ledger :=
  let row := BinaryPRGOutputRun.originalSample prepared.request rich bits
  let frame := prepared.header.bytes ++ BinaryStoredRowFrame.words (List.ofFn row.1.read)
  let visits := BinaryStoredRowFrameWork.wordsVisits (List.ofFn row.1.read) + 2 * n + prepared.header.bytes.length
  (frame,{row.2 with coordinateFraming := visits})

theorem output_state {n : ℕ} (prepared : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n prepared.request.precision) → Bool) :
    output prepared rich bits = BinaryPRGOutputRun.output prepared.request rich bits := by
  unfold output BinaryPRGOutputRun.output BinaryStoredRowFrame.row BinaryStoredRowFrameWork.rowCoordinateVisits
  simp only [prepared.header.correct]

def run (rich : Bool) (request seed : List Bool) : Option (List Bool × BinaryPRGOutputRun.Ledger) × Ledger :=
  let decoded := read request
  let result := decoded.1.bind (fun parsed =>
    if parsed.2 = [] then
      (RationalPRGBinaryRequest.seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.request.precision) seed).map
        (fun table => output parsed.1.2 rich table.read)
    else none)
  (result,decoded.2)

theorem run_state (rich : Bool) (request seed : List Bool) :
    (run rich request seed).1 = BinaryPRGOutputRun.run rich request seed := by
  have hr := read_state request
  cases h : (read request).1 with
  | none =>
      rw [h,Option.map_none] at hr
      simp only [run,h,BinaryPRGOutputRun.run,← hr,Option.bind_none]
  | some parsed =>
      rw [h,Option.map_some] at hr
      simp only [run,h,BinaryPRGOutputRun.run,← hr,Option.bind_some,forget]
      split
      · simp only [output_state]
      · rfl

theorem run_prefix (rich : Bool) (request seed : List Bool) : (run rich request seed).2 = (read request).2 := rfl

theorem run_returned_budget (rich : Bool) (request seed : List Bool) (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (run rich request seed).1 = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords request = some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1 (if rich then parsed.2.source.a else parsed.2.source.b) returned.1 := by
  rw [run_state] at h
  exact BinaryPRGOutputRun.run_returned_budget rich request seed returned h

theorem run_output_recorded_bound (rich : Bool) (request seed : List Bool) (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (run rich request seed).1 = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      BinaryPRGRequest.read request = some (parsed,[]) ∧ returned.2.recorded ≤ BinaryPRGOutputRun.bound parsed.2 := by
  rw [run_state] at h
  exact BinaryPRGOutputRun.run_recorded_bound rich request seed returned h

def inputBound (length : ℕ) : ℕ := BinaryPRGStoredDimensionFrame.bound length + BinaryDecodedInputLength.preparationFrameBound length

theorem read_input_bound (bits : List Bool) : (read bits).2.recorded ≤ inputBound bits.length := by
  have hr := read_recorded_bound bits
  cases he : (BinaryPRGStoredDimensionFrame.read bits).1 with
  | none =>
      simp only [he,Nat.add_zero] at hr
      exact hr.trans (Nat.le_add_right _ _)
  | some parsed =>
      simp only [he] at hr
      have hOld : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed :=
        (BinaryPRGNormalizedFrameWork.read_state bits).trans ((BinaryPRGStoredDimensionFrame.read_state bits).symm.trans he)
      exact hr.trans (Nat.add_le_add_left (BinaryDecodedInputLength.parsed_preparation_bound bits parsed hOld) _)

def polynomialBound (length : ℕ) : ℕ := 8614755038 * (length + 1) ^ 4

theorem inputBound_polynomial (length : ℕ) : inputBound length ≤ polynomialBound length := by
  unfold inputBound polynomialBound
  calc
    _ ≤ 538 * (length + 1) ^ 4 + 8614754500 * (length + 1) ^ 4 :=
      Nat.add_le_add (BinaryPRGStoredDimensionFrame.bound_polynomial length) (BinaryPRGInputPolynomial.preparationFrame_bound length)
    _ = _ := by ring

theorem read_polynomial (bits : List Bool) : (read bits).2.recorded ≤ polynomialBound bits.length :=
  (read_input_bound bits).trans (inputBound_polynomial bits.length)

theorem run_input_bound (rich : Bool) (request seed : List Bool) :
    (run rich request seed).2.recorded ≤ inputBound request.length := read_input_bound request

theorem run_polynomial (rich : Bool) (request seed : List Bool) :
    (run rich request seed).2.recorded ≤ polynomialBound request.length := read_polynomial request

end Blotto.BinaryPRGStoredDimensionRequest
