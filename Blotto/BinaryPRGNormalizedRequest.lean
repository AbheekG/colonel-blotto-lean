import Blotto.BinaryPRGNormalizedFrameWork
import Blotto.BinaryPRGHeaderFrame
import Blotto.BinaryPRGOutputRun

/-! The raw request joins actual measured canonical game framing with
retained Boolean header and promise/numerical preparation. Complete request/
frame/rejection/readback/output scopes remain exact. Actual frame length derives
all recorded frame/header/normalization prices; dimension/precision/seed/control/
bookkeeping and complete model/physical-space claims remain separate. -/

namespace Blotto.BinaryPRGNormalizedRequest
open BinaryRationalNormalization BinaryPRGPreparation

structure Request (n : ℕ) where
  request : BinaryPRGRequest.Request n
  header : BinaryPRGHeaderFrame.Header n

structure Ledger where
  frame : BinaryPRGNormalizedFrameWork.Ledger
  preparation : BinaryPRGMeasuredPreparation.Ledger
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.frame.recorded + ledger.preparation.recorded

def read (bits : List Bool) : Option ((Σ n, Request n) × List Bool) × Ledger :=
  let game := BinaryPRGNormalizedFrameWork.read bits
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
  have hv := BinaryPRGNormalizedFrameWork.read_state bits
  cases h : (BinaryPRGNormalizedFrameWork.read bits).1 with
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

theorem read_ledger_frame (bits : List Bool) : (read bits).2.frame = (BinaryPRGNormalizedFrameWork.read bits).2 := by
  unfold read
  dsimp only
  split <;> rfl

theorem read_ledger_bound (bits : List Bool) :
    (read bits).2.recorded ≤ (BinaryPRGNormalizedFrameWork.read bits).2.recorded +
      match (BinaryPRGNormalizedFrameWork.read bits).1 with
      | none => 0
      | some parsed => BinaryPRGMeasuredPreparation.bound parsed.1.2.game.input := by
  unfold read
  dsimp only
  split
  · exact Nat.le_refl _
  · rename_i parsed hp
    exact Nat.add_le_add_left (BinaryPRGMeasuredPreparation.prepareChecked_bound parsed.1.2.game.input parsed.1.2.game.canonical) _

theorem read_frame_bound (bits : List Bool) : (read bits).2.frame.recorded ≤ BinaryPRGNormalizedFrameWork.bound bits.length := by
  rw [read_ledger_frame]
  exact BinaryPRGNormalizedFrameWork.read_bound bits

theorem read_recorded_bound (bits : List Bool) :
    (read bits).2.recorded ≤ BinaryPRGNormalizedFrameWork.bound bits.length +
      match (BinaryPRGNormalizedFrameWork.read bits).1 with
      | none => 0
      | some parsed => BinaryPRGMeasuredPreparation.bound parsed.1.2.game.input := by
  have hr := read_ledger_bound bits
  have hf := BinaryPRGNormalizedFrameWork.read_bound bits
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

end Blotto.BinaryPRGNormalizedRequest
