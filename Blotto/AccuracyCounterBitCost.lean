import Blotto.AccuracyCounterWork
import Blotto.BinaryPayloadMergeBitWork

/-! Prices the actual small Boolean width-counter assemblies in precision
selection. The large accuracy payloads remain Boolean words. A linear shift/
add primitive envelope is explicit; decoder index metadata, allocation and
physical arithmetic implementation remain separate. -/

namespace Blotto.PositiveBinaryWord

def countedWidthMergeBitWork (primitive : ℕ → ℕ) (w : PositiveBinaryWord) : ℕ :=
  let bits := BinaryCarryCounter.count w.tail [true]
  2 * bits.length + BinaryPayload.balancedBitWork primitive bits.toArray 0 bits.length

theorem countedWidthMergeBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (w : PositiveBinaryWord) :
    countedWidthMergeBitWork primitive w ≤ (38 + 16 * c) * w.width := by
  let bits := BinaryCarryCounter.count w.tail [true]
  have hLength := BinaryCarryCounter.countFromOne_length w.tail
  have hWidth := BinaryCarryCounter.wordWidth_double w.width (by unfold width; omega)
  change bits.length ≤ binaryWordWidth w.width at hLength
  have hMerge := BinaryCarryCounter.counter_mergeSize_bound w.tail
  change BinaryPayload.mergeSize bits.length ≤ 8 * w.width at hMerge
  have hDecode := BinaryPayload.balancedBitWork_bound primitive c hPrimitive bits.toArray 0 bits.length
  have hPriced := Nat.mul_le_mul_left (4 + 2 * c) hMerge
  change 2 * bits.length + BinaryPayload.balancedBitWork primitive bits.toArray 0 bits.length ≤ (38 + 16 * c) * w.width
  nlinarith

def ratioCounterMergeBitWork (primitive : ℕ → ℕ) (a b : PositiveBinaryWord) : ℕ :=
  countedWidthMergeBitWork primitive a + countedWidthMergeBitWork primitive b +
    countedWidthMergeBitWork primitive a + countedWidthMergeBitWork primitive (b.shifted (a.width - b.width))

theorem ratioCounterMergeBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (a b : PositiveBinaryWord) :
    ratioCounterMergeBitWork primitive a b ≤ (114 + 48 * c) * (a.width + b.width) := by
  have hA := countedWidthMergeBitWork_bound primitive c hPrimitive a
  have hB := countedWidthMergeBitWork_bound primitive c hPrimitive b
  have hShift := countedWidthMergeBitWork_bound primitive c hPrimitive (b.shifted (a.width - b.width))
  rw [width_shifted] at hShift
  have hAligned : b.width + (a.width - b.width) ≤ a.width + b.width := by omega
  have hShiftBound := hShift.trans (Nat.mul_le_mul_left (38 + 16 * c) hAligned)
  unfold ratioCounterMergeBitWork
  nlinarith

end Blotto.PositiveBinaryWord
namespace Blotto.BinaryAccuracyWords

def counterBitWork (primitive : ℕ → ℕ) (a : BinaryAccuracyWords) : ℕ :=
  (a.denominator.shifted 5).ratioWidthCarryWork a.numerator +
    PositiveBinaryWord.ratioCounterMergeBitWork primitive (a.denominator.shifted 5) a.numerator

theorem counterBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (a : BinaryAccuracyWords) :
    a.counterBitWork primitive ≤ (120 + 48 * c) * (a.numerator.width + a.denominator.width + 5) := by
  have hCarry := (a.denominator.shifted 5).ratioWidthCarryWork_bound a.numerator
  have hMerge := PositiveBinaryWord.ratioCounterMergeBitWork_bound primitive c hPrimitive (a.denominator.shifted 5) a.numerator
  rw [PositiveBinaryWord.width_shifted] at hCarry hMerge
  unfold counterBitWork
  nlinarith

def readPrecisionBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  unaryReadTraversalWork frame +
    match read frame with
    | none => 0
    | some (words, _) => words.counterBitWork primitive

theorem readPrecisionBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    readPrecisionBitWork primitive frame ≤ (127 + 48 * c) * frame.length + 634 + 240 * c := by
  have hRead := unaryReadTraversalWork_bound frame
  unfold readPrecisionBitWork
  cases h : read frame with
  | none => simp only; nlinarith
  | some pair =>
    rcases pair with ⟨words, suffix⟩
    have hWidth := read_width_bound frame suffix words h
    have hCounter := counterBitWork_bound primitive c hPrimitive words
    have hSum : words.numerator.width + words.denominator.width + 5 ≤ frame.length + 5 := by omega
    have hPrice := hCounter.trans (Nat.mul_le_mul_left (120 + 48 * c) hSum)
    simp only
    nlinarith

end Blotto.BinaryAccuracyWords
