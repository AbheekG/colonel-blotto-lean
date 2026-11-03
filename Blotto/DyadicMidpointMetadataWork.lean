import Blotto.DyadicMidpointDecodeWork
import Blotto.IndexedLoopMetadataWork
import Blotto.BinaryPayloadBufferMetadata
import Blotto.RationalPreparationCommonPrice

/-! The primary midpoint's Array.ofFn construction, balanced index decoder and
small scalar control add explicit metadata prices. Buffer pushes may copy the
complete old prefix. Bit-reader address/offset, physical backend/records and
ownership/space remain separate. -/

namespace Blotto

def dyadicMidpointMetadataBitWork (primitive : ℕ → ℕ) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  indexedLoopMetadataBitWork primitive 0 K + BinaryPayload.bufferCopyWork K 0 +
    BinaryPayload.indexMetadataBitWork primitive (Array.ofFn bits) 0 K +
      6 * binaryWordWidth (K + 2) + 3 * primitive (binaryWordWidth (K + 2)) + 6

def dyadicMidpointMetadataBound (c K : ℕ) : ℕ :=
  indexedLoopMetadataBound c K + K * (K + 1) +
    (2 * K + 1) * ((12 + 6 * c) * binaryWordWidth (2 * K + 4) + 8) +
      (6 + 3 * c) * binaryWordWidth (K + 2) + 6

theorem dyadicMidpointMetadataBound_mono (c : ℕ) : Monotone (dyadicMidpointMetadataBound c) := by
  intro a b hab
  have hLoop := indexedLoopMetadataBound_mono c hab
  have hDecoderWidth := binaryWordWidth_mono (show 2 * a + 4 ≤ 2 * b + 4 by omega)
  have hScalarWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 2)
  unfold dyadicMidpointMetadataBound
  gcongr

theorem dyadicMidpointMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    dyadicMidpointMetadataBitWork primitive K bits ≤ dyadicMidpointMetadataBound c K := by
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive K
  have hIndex := BinaryPayload.indexMetadataBitWork_bound primitive c hPrimitive (Array.ofFn bits) 0 K
  have hWidth : BinaryPayload.indexMetadataWordWidth (Array.ofFn bits) 0 K = binaryWordWidth (2 * K + 4) := by
    simp only [BinaryPayload.indexMetadataWordWidth, Array.size_ofFn, Nat.add_zero]
    congr 1
    omega
  rw [hWidth] at hIndex
  have hScalar := hPrimitive (binaryWordWidth (K + 2))
  have hScalarPrice : 6 * binaryWordWidth (K + 2) + 3 * primitive (binaryWordWidth (K + 2)) + 6 ≤
      (6 + 3 * c) * binaryWordWidth (K + 2) + 6 := by nlinarith
  unfold dyadicMidpointMetadataBitWork dyadicMidpointMetadataBound
  rw [BinaryPayload.bufferCopyWork_eq]
  simp only [Nat.mul_zero, Nat.zero_add]
  omega

noncomputable def dyadicMidpointCompleteAvailableWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  dyadicMidpointDecodeBitWork model primitive K bits + dyadicMidpointMetadataBitWork primitive K bits

theorem dyadicMidpointCompleteAvailableWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    dyadicMidpointCompleteAvailableWork model primitive K bits ≤
      RationalNestedInput.preparationNumericBitWork c K +
        11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) + dyadicMidpointMetadataBound c K :=
  Nat.add_le_add (dyadicMidpointDecodeBitWork_bound model primitive c hPrimitive K bits)
    (dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K bits)

end Blotto
