import Blotto.BinaryFrameLengthMetadata
import Blotto.RationalPRGParsedCheckCost

/-! Additional row-count and suffix-length integer work follows the existing
game parser's branch order. Bounds include failed reads and huge dimensions.
Primitive/copy labels remain distinct from physical decoder addresses/records. -/

namespace Blotto.RationalPRGBinaryInput

def rawMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  BinaryNatFrame.lengthMetadataBitWork primitive frame +
    match BinaryNatFrame.read frame with
    | none => 0
    | some dim => BinaryRatFrame.lengthMetadataBitWork primitive dim.2 +
      match BinaryRatFrame.read dim.2 with
      | none => 0
      | some first => BinaryRatFrame.lengthMetadataBitWork primitive first.2 +
        match BinaryRatFrame.read first.2 with
        | none => 0
        | some second => BinaryRatListFrame.lengthMetadataBitWork primitive dim.1 second.2 +
          BinaryRatListFrame.counterBitWork primitive dim.1 second.2

def rawMetadataBound (c length : ℕ) : ℕ :=
  (2 * length + 7) * BinaryNatFrame.lengthMetadataBound c length +
    (length + 1) * ((4 + 2 * c) * (length + 1) + 1)

theorem rawMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    rawMetadataBitWork primitive frame ≤ rawMetadataBound c frame.length := by
  let M := BinaryNatFrame.lengthMetadataBound c frame.length
  let C := (frame.length + 1) * ((4 + 2 * c) * (frame.length + 1) + 1)
  have hNat := BinaryNatFrame.lengthMetadataBitWork_bound primitive c hPrimitive frame
  change BinaryNatFrame.lengthMetadataBitWork primitive frame ≤ M at hNat
  have hRat : ∀ tail : List Bool, tail.length ≤ frame.length →
      BinaryRatFrame.lengthMetadataBitWork primitive tail ≤ 2 * M := by
    intro tail hTail
    exact (BinaryRatFrame.lengthMetadataBitWork_bound primitive c hPrimitive tail).trans
      (Nat.mul_le_mul_left 2 (BinaryNatFrame.lengthMetadataBound_mono c hTail))
  unfold rawMetadataBitWork
  cases hDim : BinaryNatFrame.read frame with
  | none => simp only; unfold rawMetadataBound; change _ ≤ (2 * frame.length + 7) * M + C; nlinarith
  | some dim =>
    rcases dim with ⟨count, tail⟩
    have hTail := BinaryNatFrame.read_suffix_length frame count tail hDim
    have hWidth := BinaryNatFrame.read_value_wordWidth frame count tail hDim
    have hA := hRat tail hTail
    simp only
    cases hFirst : BinaryRatFrame.read tail with
    | none =>
      simp only
      change _ ≤ (2 * frame.length + 7) * M + C
      nlinarith
    | some first =>
      rcases first with ⟨a, rest⟩
      have hRest := (BinaryRatFrame.read_suffix_length tail a rest hFirst).trans hTail
      have hB := hRat rest hRest
      simp only
      cases hSecond : BinaryRatFrame.read rest with
      | none =>
        simp only
        change _ ≤ (2 * frame.length + 7) * M + C
        nlinarith
      | some second =>
        rcases second with ⟨b, remaining⟩
        have hRemaining := (BinaryRatFrame.read_suffix_length rest b remaining hSecond).trans hRest
        have hRow := (BinaryRatListFrame.lengthMetadataBitWork_bound primitive c hPrimitive count remaining).trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hRemaining 1))
            (BinaryNatFrame.lengthMetadataBound_mono c hRemaining))
        have hCounter := (BinaryRatListFrame.counterBitWork_bound primitive c hPrimitive count remaining).trans
          (Nat.mul_le_mul (Nat.add_le_add_right hRemaining 1)
            (Nat.add_le_add_right (Nat.mul_le_mul_left (4 + 2 * c) hWidth) 1))
        change BinaryRatListFrame.lengthMetadataBitWork primitive count remaining ≤ 2 * (frame.length + 1) * M at hRow
        change BinaryRatListFrame.counterBitWork primitive count remaining ≤ C at hCounter
        simp only
        change _ ≤ (2 * frame.length + 7) * M + C
        nlinarith

end Blotto.RationalPRGBinaryInput
