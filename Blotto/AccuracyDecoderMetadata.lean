import Blotto.BinaryPayloadBufferMetadata
import Blotto.AccuracyCounterBitCost

/-! The precision selector decodes only canonical small width counters.
Their square-length bound makes even conservative full-prefix buffer copying
linear in the original Boolean word width. Physical addresses/backend records
and final scalar precision/index bookkeeping remain separate. -/

namespace Blotto.BinaryPayload

theorem decoderMetadataBound_square_bound (c length : ℕ) :
    decoderMetadataBound c length ≤ (147 + 64 * c) * (length + 1) ^ 2 := by
  have hWidthA : binaryWordWidth (length + 1) ≤ 2 * (length + 1) := by
    have h := Nat.log2_le_self (length + 1)
    unfold binaryWordWidth
    omega
  have hWidthB : binaryWordWidth (2 * length + 4) ≤ 5 * (length + 1) := by
    have h := Nat.log2_le_self (2 * length + 4)
    unfold binaryWordWidth
    omega
  have hLength := Nat.mul_le_mul_left (length + 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left (c + 2) hWidthA) 1)
  have hIndex := Nat.mul_le_mul_left (2 * length + 1)
    (Nat.add_le_add_right (Nat.mul_le_mul_left (12 + 6 * c) hWidthB) 8)
  unfold decoderMetadataBound BinaryNatFrame.lengthMetadataBound
  nlinarith

end Blotto.BinaryPayload
namespace Blotto.PositiveBinaryWord

def countedWidthDecoderMetadataBitWork (primitive : ℕ → ℕ) (w : PositiveBinaryWord) : ℕ :=
  BinaryPayload.decoderMetadataBitWork primitive (BinaryCarryCounter.count w.tail [true])

theorem countedWidthDecoderMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (w : PositiveBinaryWord) :
    countedWidthDecoderMetadataBitWork primitive w ≤ (1323 + 576 * c) * w.width := by
  let bits := BinaryCarryCounter.count w.tail [true]
  have hCanonical := BinaryCarryCounter.count_canonical w.tail [true] ⟨trivial, fun _ => rfl⟩
  have hValue : BinaryCarryCounter.value bits = w.width := by
    rw [BinaryCarryCounter.count_value]
    change 1 + w.tail.length = w.width
    unfold width
    omega
  have hSquare := BinaryCarryCounter.canonical_square_bound bits hCanonical
  rw [hValue] at hSquare
  have hLength := BinaryCarryCounter.countFromOne_length w.tail
  have hWidth := BinaryCarryCounter.wordWidth_double w.width (by unfold width; omega)
  change bits.length ≤ binaryWordWidth w.width at hLength
  have hPos : 1 ≤ w.width := by unfold width; omega
  have hPadded : (bits.length + 1) ^ 2 ≤ 9 * w.width := by nlinarith
  have hMetadata := (BinaryPayload.decoderMetadataBitWork_bound primitive c hPrimitive bits).trans
    (BinaryPayload.decoderMetadataBound_square_bound c bits.length)
  have hPrice := Nat.mul_le_mul_left (147 + 64 * c) hPadded
  change BinaryPayload.decoderMetadataBitWork primitive bits ≤ (1323 + 576 * c) * w.width
  nlinarith

def ratioDecoderMetadataBitWork (primitive : ℕ → ℕ) (a b : PositiveBinaryWord) : ℕ :=
  countedWidthDecoderMetadataBitWork primitive a + countedWidthDecoderMetadataBitWork primitive b +
    countedWidthDecoderMetadataBitWork primitive a + countedWidthDecoderMetadataBitWork primitive (b.shifted (a.width - b.width))

theorem ratioDecoderMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (a b : PositiveBinaryWord) :
    ratioDecoderMetadataBitWork primitive a b ≤ (3969 + 1728 * c) * (a.width + b.width) := by
  have hA := countedWidthDecoderMetadataBitWork_bound primitive c hPrimitive a
  have hB := countedWidthDecoderMetadataBitWork_bound primitive c hPrimitive b
  have hShift := countedWidthDecoderMetadataBitWork_bound primitive c hPrimitive (b.shifted (a.width - b.width))
  rw [width_shifted] at hShift
  have hAligned : b.width + (a.width - b.width) ≤ a.width + b.width := by omega
  have hShiftBound := hShift.trans (Nat.mul_le_mul_left (1323 + 576 * c) hAligned)
  unfold ratioDecoderMetadataBitWork
  nlinarith

end Blotto.PositiveBinaryWord
namespace Blotto.BinaryAccuracyWords

def decoderMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  match read frame with
  | none => 0
  | some (words, _) => PositiveBinaryWord.ratioDecoderMetadataBitWork primitive (words.denominator.shifted 5) words.numerator

theorem decoderMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    decoderMetadataBitWork primitive frame ≤ (3969 + 1728 * c) * (frame.length + 5) := by
  unfold decoderMetadataBitWork
  cases hRead : read frame with
  | none => exact Nat.zero_le _
  | some pair =>
    rcases pair with ⟨words, suffix⟩
    have hSize := read_width_bound frame suffix words hRead
    have hWork := PositiveBinaryWord.ratioDecoderMetadataBitWork_bound primitive c hPrimitive (words.denominator.shifted 5) words.numerator
    rw [PositiveBinaryWord.width_shifted] at hWork
    exact hWork.trans (Nat.mul_le_mul_left (3969 + 1728 * c) (by omega))

end Blotto.BinaryAccuracyWords
