import Blotto.BinaryUnaryPayloadMeasured
import Blotto.BinaryStoredDimensionControlMeasured
import Blotto.BinaryPositiveWordLifetime

/-! The positive-word reader consumes an actual reversed payload and the
actual measured leading-zero loop. It preserves malformed/zero/truncated
rejections and every suffix, without decoding the accuracy integer. -/
namespace Blotto.BinaryPositiveWordMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def parse (bits : List Bool) : (Option PositiveBinaryWord × Trace) × ℕ :=
  let trimmed := BinaryStoredDimensionControlMeasured.drop bits
  let parsed := match trimmed.1.1.1 with
    | true::tail => some (⟨tail⟩ : PositiveBinaryWord)
    | _ => none
  ((parsed,wrap 16 2 [trimmed.1.2]),trimmed.2+4)

theorem parse_erases (bits : List Bool) : (parse bits).1 = BinaryPositiveWordLifetime.parseWithTrace bits := by
  simp only [parse,BinaryPositiveWordLifetime.parseWithTrace,BinaryStoredDimensionControlMeasured.drop_erases]
  rfl

theorem parse_work (bits : List Bool) : (parse bits).2 ≤ 8*(bits.length+1) := by
  have h := BinaryStoredDimensionControlMeasured.drop_work bits
  change (BinaryStoredDimensionControlMeasured.drop bits).2+4 ≤ _
  omega

def read (frame : List Bool) : (Option (PositiveBinaryWord × List Bool) × Trace) × ℕ :=
  let raw := BinaryUnaryPayloadMeasured.readReversed frame
  match raw.1.1 with
  | none => ((none,wrap 16 2 [raw.1.2]),raw.2+4)
  | some parsed =>
      let word := parse parsed.1
      ((word.1.1.map (fun value => (value,parsed.2)),wrap 24 2 [raw.1.2,word.1.2]),raw.2+word.2+8)

theorem read_erases (frame : List Bool) : (read frame).1 = BinaryPositiveWordLifetime.readWithTrace frame := by
  unfold read BinaryPositiveWordLifetime.readWithTrace
  dsimp only
  simp only [BinaryUnaryPayloadMeasured.readReversed_erases,parse_erases]
  cases (BinaryUnaryPayloadLifetime.readReversedWithTrace frame).1 <;> rfl

theorem read_work (frame : List Bool) : (read frame).2 ≤ 32*(frame.length+1) := by
  have hr := BinaryUnaryPayloadMeasured.readReversed_work frame
  unfold read
  dsimp only
  split
  · omega
  · rename_i parsed hSome
    have hLength := BinaryUnaryPayloadLifetime.readReversed_payload_length frame parsed
      ((congrArg Prod.fst (BinaryUnaryPayloadMeasured.readReversed_erases frame)).symm.trans hSome)
    have hp := parse_work parsed.1
    omega

theorem read_consumed (frame : List Bool) (parsed : PositiveBinaryWord × List Bool)
    (h : (read frame).1.1 = some parsed) : 2*parsed.1.width+parsed.2.length+1 ≤ frame.length :=
  BinaryPositiveWordLifetime.read_consumed frame parsed ((congrArg Prod.fst (read_erases frame)).symm.trans h)

theorem read_usage (frame : List Bool) : usage (read frame).1.2 ≤ 256*(frame.length+1) := by
  rw [read_erases]
  exact BinaryPositiveWordLifetime.readWithTrace_usage frame

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (read frame).1.2 steps ≤ borrowed+frame.length+256*(frame.length+1) ∧
    framePeak ((read frame).1.2.take steps) ≤ 256*(frame.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (read_usage frame) _ steps

end Blotto.BinaryPositiveWordMeasured
