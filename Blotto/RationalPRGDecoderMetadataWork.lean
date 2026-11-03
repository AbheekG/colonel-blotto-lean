import Blotto.BinaryFramePayloadMetadata
import Blotto.AccuracyDecoderMetadata
import Blotto.RationalPRGRequestMetadataWork

/-! Adds actual numeric-frame payload and direct-accuracy small-counter
decoder metadata to the composed request. Local sampler/output container/index
work, physical addresses/backend/records/ownership/space remain separate. -/

namespace Blotto.RationalPRGBinaryInput

def rawDecoderMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  BinaryNatFrame.payloadMetadataBitWork primitive frame +
    match BinaryNatFrame.read frame with
    | none => 0
    | some dim => BinaryRatFrame.payloadMetadataBitWork primitive dim.2 +
      match BinaryRatFrame.read dim.2 with
      | none => 0
      | some first => BinaryRatFrame.payloadMetadataBitWork primitive first.2 +
        match BinaryRatFrame.read first.2 with
        | none => 0
        | some second => BinaryRatListFrame.payloadMetadataBitWork primitive dim.1 second.2

def rawDecoderMetadataBound (c length : ℕ) : ℕ :=
  (2 * length + 7) * BinaryNatFrame.payloadMetadataBound c length

theorem rawDecoderMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    rawDecoderMetadataBitWork primitive frame ≤ rawDecoderMetadataBound c frame.length := by
  let M := BinaryNatFrame.payloadMetadataBound c frame.length
  have hNat := BinaryNatFrame.payloadMetadataBitWork_bound primitive c hPrimitive frame
  change BinaryNatFrame.payloadMetadataBitWork primitive frame ≤ M at hNat
  have hRat : ∀ tail : List Bool, tail.length ≤ frame.length → BinaryRatFrame.payloadMetadataBitWork primitive tail ≤ 2 * M := by
    intro tail hTail
    exact (BinaryRatFrame.payloadMetadataBitWork_bound primitive c hPrimitive tail).trans
      (Nat.mul_le_mul_left 2 (BinaryNatFrame.payloadMetadataBound_mono c hTail))
  unfold rawDecoderMetadataBitWork
  cases hDim : BinaryNatFrame.read frame with
  | none => simp only; change _ ≤ (2 * frame.length + 7) * M; nlinarith
  | some dim =>
    rcases dim with ⟨count, tail⟩
    have hTail := BinaryNatFrame.read_suffix_length frame count tail hDim
    have hA := hRat tail hTail
    simp only
    cases hFirst : BinaryRatFrame.read tail with
    | none => simp only; change _ ≤ (2 * frame.length + 7) * M; nlinarith
    | some first =>
      rcases first with ⟨a, rest⟩
      have hRest := (BinaryRatFrame.read_suffix_length tail a rest hFirst).trans hTail
      have hB := hRat rest hRest
      simp only
      cases hSecond : BinaryRatFrame.read rest with
      | none => simp only; change _ ≤ (2 * frame.length + 7) * M; nlinarith
      | some second =>
        rcases second with ⟨b, remaining⟩
        have hRemaining := (BinaryRatFrame.read_suffix_length rest b remaining hSecond).trans hRest
        have hRow := (BinaryRatListFrame.payloadMetadataBitWork_bound primitive c hPrimitive count remaining).trans
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hRemaining 1))
            (BinaryNatFrame.payloadMetadataBound_mono c hRemaining))
        change BinaryRatListFrame.payloadMetadataBitWork primitive count remaining ≤ 2 * (frame.length + 1) * M at hRow
        simp only
        change _ ≤ (2 * frame.length + 7) * M
        nlinarith

end Blotto.RationalPRGBinaryInput
namespace Blotto.RationalPRGBinaryRequest

def decoderMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  RationalPRGBinaryInput.rawDecoderMetadataBitWork primitive frame +
    match RationalPRGBinaryInput.readChecked frame with
    | none => 0
    | some game => BinaryAccuracyWords.decoderMetadataBitWork primitive game.2

def decoderMetadataBound (c length : ℕ) : ℕ :=
  RationalPRGBinaryInput.rawDecoderMetadataBound c length + (3969 + 1728 * c) * (length + 5)

theorem decoderMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    decoderMetadataBitWork primitive frame ≤ decoderMetadataBound c frame.length := by
  have hGame := RationalPRGBinaryInput.rawDecoderMetadataBitWork_bound primitive c hPrimitive frame
  unfold decoderMetadataBitWork
  cases hParsed : RationalPRGBinaryInput.readChecked frame with
  | none => simp only; unfold decoderMetadataBound; omega
  | some game =>
    rcases game with ⟨input, suffix⟩
    have hSuffix := (RationalPRGBinaryInput.readChecked_bounds frame input suffix hParsed).2
    have hAccuracy := BinaryAccuracyWords.decoderMetadataBitWork_bound primitive c hPrimitive suffix
    have hPrice := Nat.mul_le_mul_left (3969 + 1728 * c) (Nat.add_le_add_right hSuffix 5)
    simp only
    unfold decoderMetadataBound
    omega

noncomputable def executionWithDecoderMetadataBitWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithGameMetadataBitWork model primitive copyResources rich frame seed + decoderMetadataBitWork primitive frame

theorem executionWithDecoderMetadataBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithDecoderMetadataBitWork model primitive copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length :=
  Nat.add_le_add (executionWithGameMetadataBitWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (decoderMetadataBitWork_bound primitive c hPrimitive frame)

end Blotto.RationalPRGBinaryRequest
