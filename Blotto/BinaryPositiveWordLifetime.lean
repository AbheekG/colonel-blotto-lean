import Blotto.BinaryStoredDimensionHeaderLifetime
import Blotto.BinaryPositiveWordReadWork

/-! Reversed payload cursors feed actual leading-zero trimming and positive
word construction. Zero, malformed and truncated payloads reject identically.
No accuracy integer is decoded; incoming cells and suffixes stay borrowed. -/
namespace Blotto.BinaryPositiveWordLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def parseWithTrace (bits : List Bool) : Option PositiveBinaryWord × Trace :=
  let trimmed := BinaryStoredDimensionHeaderLifetime.dropWithTrace bits
  let parsed := match trimmed.1.1 with
    | true::tail => some (⟨tail⟩ : PositiveBinaryWord)
    | _ => none
  (parsed,wrap 16 2 [trimmed.2])

theorem parseWithTrace_state (bits : List Bool) : (parseWithTrace bits).1 = PositiveBinaryWord.parse bits := by
  simp only [parseWithTrace,BinaryStoredDimensionHeaderLifetime.dropWithTrace_state,PositiveBinaryWord.parse]
  rfl

theorem parseWithTrace_usage (bits : List Bool) : usage (parseWithTrace bits).2 ≤ 64*(bits.length+1) := by
  have h := BinaryStoredDimensionHeaderLifetime.dropWithTrace_usage bits
  have hw := wrap_usage 16 2 [(BinaryStoredDimensionHeaderLifetime.dropWithTrace bits).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (parseWithTrace bits).2 ≤ _ at hw
  omega

def readWithTrace (frame : List Bool) : Option (PositiveBinaryWord × List Bool) × Trace :=
  let raw := BinaryUnaryPayloadLifetime.readReversedWithTrace frame
  match raw.1 with
  | none => (none,wrap 16 2 [raw.2])
  | some parsed =>
      let word := parseWithTrace parsed.1
      (word.1.map (fun value => (value,parsed.2)),wrap 24 2 [raw.2,word.2])

theorem readWithTrace_state (frame : List Bool) : (readWithTrace frame).1 = PositiveBinaryWord.read frame := by
  unfold readWithTrace PositiveBinaryWord.read
  dsimp only
  rw [BinaryUnaryPayloadLifetime.readReversedWithTrace_state]
  cases UnaryPayload.readReversed frame with
  | none => rfl
  | some parsed => simp only [Option.bind_some,parseWithTrace_state]

theorem readWithTrace_usage (frame : List Bool) : usage (readWithTrace frame).2 ≤ 256*(frame.length+1) := by
  have hRaw := BinaryUnaryPayloadLifetime.readReversedWithTrace_usage frame
  unfold readWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [(BinaryUnaryPayloadLifetime.readReversedWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [(BinaryUnaryPayloadLifetime.readReversedWithTrace frame).2]) ≤ _
    omega
  · rename_i parsed hSome
    have hLength := BinaryUnaryPayloadLifetime.readReversed_payload_length frame parsed hSome
    have hParse := parseWithTrace_usage parsed.1
    have hw := wrap_usage 24 2 [(BinaryUnaryPayloadLifetime.readReversedWithTrace frame).2,(parseWithTrace parsed.1).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [(BinaryUnaryPayloadLifetime.readReversedWithTrace frame).2,(parseWithTrace parsed.1).2]) ≤ _
    omega

theorem read_consumed (frame : List Bool) (parsed : PositiveBinaryWord × List Bool)
    (h : (readWithTrace frame).1 = some parsed) : 2*parsed.1.width+parsed.2.length+1 ≤ frame.length :=
  PositiveBinaryWord.read_width_bound frame parsed.2 parsed.1 ((readWithTrace_state frame).symm.trans h)

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (readWithTrace frame).2 steps ≤ borrowed+frame.length+256*(frame.length+1) ∧
    framePeak ((readWithTrace frame).2.take steps) ≤ 256*(frame.length+1) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) _ steps

end Blotto.BinaryPositiveWordLifetime
