import Blotto.BinaryPayloadIndexMetadata
import Blotto.BinaryListLengthWork
import Blotto.BinaryFrameLengthMetadata

/-! Decoder preparation and index metadata use the actual payload buffer and
length. Array pushes may copy every previous Boolean cell; no exclusive-owner
assumption is used. Integer counters, payload copies and recursive index work
are included, while physical addresses/allocator records remain separate. -/

namespace Blotto.BinaryPayload

def bufferCopyWork : ℕ → ℕ → ℕ
  | 0, _ => 0
  | length + 1, prefixCells => 2 * (prefixCells + 1) + bufferCopyWork length (prefixCells + 1)

theorem bufferCopyWork_eq (length prefixCells : ℕ) : bufferCopyWork length prefixCells = length * (2 * prefixCells + length + 1) := by
  induction length generalizing prefixCells with
  | zero => simp [bufferCopyWork]
  | succ length ih => rw [bufferCopyWork, ih]; ring

def decoderMetadataBitWork (primitive : ℕ → ℕ) (payload : List Bool) : ℕ :=
  2 * listLengthBitWork primitive 0 payload + bufferCopyWork payload.length 0 +
    indexMetadataBitWork primitive payload.toArray 0 payload.length

def decoderMetadataBound (c length : ℕ) : ℕ :=
  2 * BinaryNatFrame.lengthMetadataBound c length + length * (length + 1) +
    (2 * length + 1) * ((12 + 6 * c) * binaryWordWidth (2 * length + 4) + 8)

theorem decoderMetadataBound_mono (c : ℕ) : Monotone (decoderMetadataBound c) := by
  intro a b hab
  have hLength := BinaryNatFrame.lengthMetadataBound_mono c hab
  have hWidth := binaryWordWidth_mono (show 2 * a + 4 ≤ 2 * b + 4 by omega)
  unfold decoderMetadataBound
  gcongr

theorem decoderMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (payload : List Bool) :
    decoderMetadataBitWork primitive payload ≤ decoderMetadataBound c payload.length := by
  have hCounter := listLengthBitWork_bound primitive c hPrimitive 0 payload
  simp only [Nat.zero_add] at hCounter
  have hIndex := indexMetadataBitWork_bound primitive c hPrimitive payload.toArray 0 payload.length
  have hWidth : indexMetadataWordWidth payload.toArray 0 payload.length = binaryWordWidth (2 * payload.length + 4) := by
    simp only [indexMetadataWordWidth, List.size_toArray, Nat.add_zero]
    congr 1
    omega
  rw [hWidth] at hIndex
  unfold decoderMetadataBitWork decoderMetadataBound
  rw [bufferCopyWork_eq]
  simp only [Nat.mul_zero, Nat.zero_add]
  change listLengthBitWork primitive 0 payload ≤ BinaryNatFrame.lengthMetadataBound c payload.length at hCounter
  omega

end Blotto.BinaryPayload
