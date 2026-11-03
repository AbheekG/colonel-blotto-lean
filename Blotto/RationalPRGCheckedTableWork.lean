import Blotto.RationalArrayConstructionWork
import Blotto.RationalPRGInputMetadataWork
import Blotto.BinaryListLengthWork

/-! Prices the checked reader's value-list length gate and table construction.
Construction permits a full old-prefix payload copy at every push and prices
an integer construction counter. Rejected length gates construct no table;
physical records, addresses and backend realization remain separate. -/

namespace Blotto.RationalPRGBinaryInput

def checkedTableBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  match read frame with
  | none => 0
  | some parsed =>
    listLengthBitWork primitive 0 parsed.1.values +
      primitive (max (binaryWordWidth parsed.1.values.length) (binaryWordWidth parsed.1.count)) +
        if parsed.1.values.length = parsed.1.count then
          rationalArrayCopyWork parsed.1.values 0 + listLengthBitWork primitive 0 parsed.1.values
        else 0

def checkedTableBound (c length : ℕ) : ℕ :=
  2 * BinaryNatFrame.lengthMetadataBound c length + c * binaryWordWidth length +
    2 * length * (length * (4 * length + 13))

theorem checkedTableBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    checkedTableBitWork primitive frame ≤ checkedTableBound c frame.length := by
  unfold checkedTableBitWork
  cases hParsed : read frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨data, suffix⟩
    have hSizes := read_wordWidths frame data suffix hParsed
    have hCount := hSizes.1
    have hLength : data.values.length ≤ frame.length := hSizes.2.1.trans_le hCount
    have hCounter := listLengthBitWork_bound primitive c hPrimitive 0 data.values
    simp only [Nat.zero_add] at hCounter
    have hCounterPrice := hCounter.trans (BinaryNatFrame.lengthMetadataBound_mono c hLength)
    have hWidthLength := binaryWordWidth_mono hLength
    have hWidthCount := binaryWordWidth_mono hCount
    have hCompare := (hPrimitive (max (binaryWordWidth data.values.length) (binaryWordWidth data.count))).trans
      (Nat.mul_le_mul_left c (max_le hWidthLength hWidthCount))
    have hWords := rationalWordWidth_sum_bound data.values (4 * frame.length + 13) hSizes.2.2.2.2
    have hCopy := rationalArrayCopyWork_bound data.values 0
    simp only [Nat.zero_add] at hCopy
    have hCopyPrice := hCopy.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hLength)
      (hWords.trans (Nat.mul_le_mul_right (4 * frame.length + 13) hLength)))
    simp only
    split <;> unfold checkedTableBound <;> omega

end Blotto.RationalPRGBinaryInput
