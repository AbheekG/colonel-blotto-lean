import Blotto.BinaryRouteDecodingWork
import Blotto.BinaryFrameLengthMetadata
import Blotto.BinaryFramePayloadMetadata

/-! Route decoding retains suffix-length and payload/buffer/index metadata
for its optional group index and two rational integer frames. Only selected
successful index branches pay rational decoding metadata. -/

namespace Blotto.BinaryRouteFrame

def ratMetadataWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  BinaryRatFrame.lengthMetadataBitWork primitive frame + BinaryRatFrame.payloadMetadataBitWork primitive frame

def naturalMetadataBound (c length : ℕ) : ℕ :=
  BinaryNatFrame.lengthMetadataBound c length + BinaryNatFrame.payloadMetadataBound c length

theorem ratMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (frame : List Bool) : ratMetadataWork primitive frame ≤ 2 * naturalMetadataBound c frame.length := by
  have hl := BinaryRatFrame.lengthMetadataBitWork_bound primitive c hPrimitive frame
  have hp := BinaryRatFrame.payloadMetadataBitWork_bound primitive c hPrimitive frame
  unfold ratMetadataWork naturalMetadataBound
  omega

theorem naturalMetadataBound_mono (c : ℕ) : Monotone (naturalMetadataBound c) := by
  intro a b hab
  exact Nat.add_le_add (BinaryNatFrame.lengthMetadataBound_mono c hab) (BinaryNatFrame.payloadMetadataBound_mono c hab)

def decoderMetadataWork (primitive : ℕ → ℕ) (m : ℕ) : List Bool → ℕ
  | [] => 0
  | false :: rest => ratMetadataWork primitive rest
  | true :: rest => BinaryNatFrame.lengthMetadataBitWork primitive rest + BinaryNatFrame.payloadMetadataBitWork primitive rest +
      match BinaryNatFrame.read rest with
      | none => 0
      | some parsed => if parsed.1 < m then ratMetadataWork primitive parsed.2 else 0

theorem decoderMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (m : ℕ) (frame : List Bool) : decoderMetadataWork primitive m frame ≤ 3 * naturalMetadataBound c frame.length := by
  cases frame with
  | nil => exact Nat.zero_le _
  | cons tag rest =>
    have hRest : rest.length ≤ (tag :: rest).length := by simp
    have hr := (ratMetadataWork_bound primitive c hPrimitive rest).trans (Nat.mul_le_mul_left 2 (naturalMetadataBound_mono c hRest))
    cases tag with
    | false => exact hr.trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 3))
    | true =>
      have hNat := Nat.add_le_add (BinaryNatFrame.lengthMetadataBitWork_bound primitive c hPrimitive rest)
        (BinaryNatFrame.payloadMetadataBitWork_bound primitive c hPrimitive rest)
      have hNatFull := hNat.trans (naturalMetadataBound_mono c hRest)
      change BinaryNatFrame.lengthMetadataBitWork primitive rest + BinaryNatFrame.payloadMetadataBitWork primitive rest +
        (match BinaryNatFrame.read rest with | none => 0 | some parsed => if parsed.1 < m then ratMetadataWork primitive parsed.2 else 0) ≤ _
      cases hParsed : BinaryNatFrame.read rest with
      | none => dsimp only; omega
      | some parsed =>
        rcases parsed with ⟨index, tail⟩
        have hTail := BinaryNatFrame.read_suffix_length rest index tail hParsed
        have ht := (ratMetadataWork_bound primitive c hPrimitive tail).trans
          (Nat.mul_le_mul_left 2 (naturalMetadataBound_mono c (hTail.trans hRest)))
        dsimp only
        split <;> omega

end Blotto.BinaryRouteFrame
