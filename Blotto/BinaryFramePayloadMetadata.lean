import Blotto.BinaryPayloadBufferMetadata
import Blotto.BinaryPrefixCounterWork

/-! Numeric frame payload preparation adds take/drop counter words and the
balanced decoder's buffer/index metadata. Truncated or missing-prefix frames
construct no payload. Suffix sharing, addresses/records and physical backend
contracts remain separate from these integer/cell prices. -/

namespace Blotto.BinaryNatFrame

def payloadMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  match scanWidth 0 frame with
  | none => 0
  | some pair => if pair.1 ≤ pair.2.length then
      2 * prefixCounterBitWork primitive pair.1 pair.2 + BinaryPayload.decoderMetadataBitWork primitive (pair.2.take pair.1)
    else 0

def payloadMetadataBound (c length : ℕ) : ℕ :=
  2 * (length + 1) * ((4 + 2 * c) * binaryWordWidth length + 1) + BinaryPayload.decoderMetadataBound c length

theorem payloadMetadataBound_mono (c : ℕ) : Monotone (payloadMetadataBound c) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono hab
  have hDecode := BinaryPayload.decoderMetadataBound_mono c hab
  unfold payloadMetadataBound
  gcongr

theorem payloadMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    payloadMetadataBitWork primitive frame ≤ payloadMetadataBound c frame.length := by
  unfold payloadMetadataBitWork
  cases hScan : scanWidth 0 frame with
  | none => exact Nat.zero_le _
  | some pair =>
    rcases pair with ⟨width, rest⟩
    have hSize := scanWidth_length 0 frame width rest hScan
    have hRest : rest.length ≤ frame.length := by omega
    have hWidth : width ≤ frame.length := by omega
    have hCounter := (prefixCounterBitWork_bound primitive c hPrimitive width rest).trans
      (Nat.mul_le_mul (Nat.add_le_add_right hRest 1)
        (Nat.add_le_add_right (Nat.mul_le_mul_left (4 + 2 * c) (binaryWordWidth_mono hWidth)) 1))
    have hPayloadLength : (rest.take width).length ≤ frame.length := by simp only [List.length_take]; omega
    have hDecode := (BinaryPayload.decoderMetadataBitWork_bound primitive c hPrimitive (rest.take width)).trans
      (BinaryPayload.decoderMetadataBound_mono c hPayloadLength)
    dsimp only
    split
    · unfold payloadMetadataBound
      nlinarith
    · exact Nat.zero_le _

end Blotto.BinaryNatFrame
namespace Blotto.BinaryRatFrame

def payloadMetadataBitWork (primitive : ℕ → ℕ) : List Bool → ℕ
  | [] => 0
  | _ :: bits => BinaryNatFrame.payloadMetadataBitWork primitive bits +
    match BinaryNatFrame.read bits with
    | none => 0
    | some first => BinaryNatFrame.payloadMetadataBitWork primitive first.2

theorem payloadMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    payloadMetadataBitWork primitive frame ≤ 2 * BinaryNatFrame.payloadMetadataBound c frame.length := by
  cases frame with
  | nil => exact Nat.zero_le _
  | cons negative bits =>
    have hFirst := BinaryNatFrame.payloadMetadataBitWork_bound primitive c hPrimitive bits
    have hFirstPrice := BinaryNatFrame.payloadMetadataBound_mono c (show bits.length ≤ (negative :: bits).length by simp)
    simp only [payloadMetadataBitWork]
    cases hRead : BinaryNatFrame.read bits with
    | none => simp only; omega
    | some first =>
      rcases first with ⟨n, suffix⟩
      have hSuffix := BinaryNatFrame.read_suffix_length bits n suffix hRead
      have hSecond := BinaryNatFrame.payloadMetadataBitWork_bound primitive c hPrimitive suffix
      have hSecondPrice := BinaryNatFrame.payloadMetadataBound_mono c
        (show suffix.length ≤ (negative :: bits).length by simp only [List.length_cons]; omega)
      simp only
      omega

end Blotto.BinaryRatFrame
namespace Blotto.BinaryRatListFrame

def payloadMetadataBitWork (primitive : ℕ → ℕ) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | count + 1, frame => BinaryRatFrame.payloadMetadataBitWork primitive frame +
    match BinaryRatFrame.read frame with
    | none => 0
    | some first => payloadMetadataBitWork primitive count first.2

theorem payloadMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (frame : List Bool) :
    payloadMetadataBitWork primitive count frame ≤ 2 * (frame.length + 1) * BinaryNatFrame.payloadMetadataBound c frame.length := by
  induction count generalizing frame with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hHead := BinaryRatFrame.payloadMetadataBitWork_bound primitive c hPrimitive frame
    simp only [payloadMetadataBitWork]
    cases hRead : BinaryRatFrame.read frame with
    | none =>
      simp only
      have hMul := Nat.mul_le_mul_right (BinaryNatFrame.payloadMetadataBound c frame.length)
        (show 2 ≤ 2 * (frame.length + 1) by omega)
      omega
    | some first =>
      rcases first with ⟨q, suffix⟩
      have hSuffix := BinaryRatFrame.read_suffix_lt frame q suffix hRead
      have hTail := ih suffix
      have hPrice := Nat.mul_le_mul_left (2 * (suffix.length + 1)) (BinaryNatFrame.payloadMetadataBound_mono c hSuffix.le)
      have hCount := Nat.mul_le_mul_right (BinaryNatFrame.payloadMetadataBound c frame.length)
        (show 2 * (suffix.length + 2) ≤ 2 * (frame.length + 1) by omega)
      simp only
      nlinarith

end Blotto.BinaryRatListFrame
