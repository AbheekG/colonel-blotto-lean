import Blotto.FairBitBlocks
import Blotto.BinaryWordWidthCore

/-! Index arithmetic for a shifted bit reader. Prices include offset/index/
result words and one addition primitive, without assuming read-value CSE.
Physical array addresses/backend records remain separate. -/

namespace Blotto

theorem firstBitBlock_index {R K : ℕ} (i : Fin R) : (Fin.castAdd K i).val = i.val := rfl

theorem secondBitBlock_index {R K : ℕ} (i : Fin K) : (Fin.natAdd R i).val = R + i.val := rfl

def bitBlockReadBitPrice (primitive : ℕ → ℕ) (offset index : ℕ) : ℕ :=
  2 * binaryWordWidth offset + 2 * binaryWordWidth index + binaryWordWidth (offset + index) +
    primitive (max (binaryWordWidth offset) (binaryWordWidth index)) + 1

theorem bitBlockReadBitPrice_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (offset index total : ℕ) (hIndex : offset + index < total) :
    bitBlockReadBitPrice primitive offset index ≤ (5 + c) * binaryWordWidth (total + 1) + 1 := by
  have hOffset := binaryWordWidth_mono (show offset ≤ total + 1 by omega)
  have hPosition := binaryWordWidth_mono (show index ≤ total + 1 by omega)
  have hSum := binaryWordWidth_mono (show offset + index ≤ total + 1 by omega)
  have hPrimitivePrice := (hPrimitive (max (binaryWordWidth offset) (binaryWordWidth index))).trans
    (Nat.mul_le_mul_left c (max_le hOffset hPosition))
  unfold bitBlockReadBitPrice
  nlinarith

def shiftedBitBlockReaderWork (primitive : ℕ → ℕ) (R K : ℕ) : ℕ :=
  ∑ j : Fin K, bitBlockReadBitPrice primitive R j.val

theorem shiftedBitBlockReaderWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (R K : ℕ) :
    shiftedBitBlockReaderWork primitive R K ≤ K * ((5 + c) * binaryWordWidth (R + K + 1) + 1) := by
  calc
    _ ≤ ∑ _j : Fin K, ((5 + c) * binaryWordWidth (R + K + 1) + 1) := Finset.sum_le_sum (fun j _ =>
      bitBlockReadBitPrice_bound primitive c hPrimitive R j.val (R + K) (by omega))
    _ = _ := by simp

end Blotto
