import Blotto.BinaryPayloadCounts

/-! Index/length words and natural primitive prices follow the balanced
decoder's actual recursion. Each node has a conservative allowance for its
length tests, split, offset, array-bound comparison and associated words.
Physical buffer addresses, allocator records and the primitive implementation
are separate. No valid-range assumption is needed for getD decoding. -/

namespace Blotto.BinaryPayload

def metadataNodeCount (length : ℕ) : ℕ :=
  if length ≤ 1 then 1 else 1 + metadataNodeCount (length / 2) + metadataNodeCount (length - length / 2)
termination_by length
decreasing_by all_goals omega

theorem metadataNodeCount_eq (length : ℕ) :
    metadataNodeCount length = if length = 0 then 1 else 2 * length - 1 := by
  unfold metadataNodeCount
  split
  · rename_i hSmall
    split <;> omega
  · rename_i hLarge
    rw [metadataNodeCount_eq, metadataNodeCount_eq]
    have hLow : length / 2 ≠ 0 := by omega
    have hHigh : length - length / 2 ≠ 0 := by omega
    rw [ite_eq_right hLow, ite_eq_right hHigh, ite_eq_right (by omega : length ≠ 0)]
    omega
termination_by length
decreasing_by all_goals omega

def indexMetadataWordWidth (buffer : Array Bool) (pos length : ℕ) : ℕ :=
  binaryWordWidth (buffer.size + pos + length + 4)

def indexMetadataBitWork (primitive : ℕ → ℕ) (buffer : Array Bool) (pos length : ℕ) : ℕ :=
  let W := indexMetadataWordWidth buffer pos length
  let step := 12 * W + 6 * primitive W + 8
  if length ≤ 1 then step else step + indexMetadataBitWork primitive buffer pos (length / 2) +
    indexMetadataBitWork primitive buffer (pos + length / 2) (length - length / 2)
termination_by length
decreasing_by all_goals omega

theorem indexMetadataBitWork_node_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (buffer : Array Bool) (pos length : ℕ) :
    indexMetadataBitWork primitive buffer pos length ≤
      metadataNodeCount length * ((12 + 6 * c) * indexMetadataWordWidth buffer pos length + 8) := by
  have hStep := hPrimitive (indexMetadataWordWidth buffer pos length)
  unfold indexMetadataBitWork
  dsimp only
  split
  · rename_i hSmall
    rw [metadataNodeCount, ite_eq_left hSmall]
    nlinarith
  · rename_i hLarge
    have hLow := indexMetadataBitWork_node_bound primitive c hPrimitive buffer pos (length / 2)
    have hHigh := indexMetadataBitWork_node_bound primitive c hPrimitive buffer (pos + length / 2) (length - length / 2)
    have hLowWidth : indexMetadataWordWidth buffer pos (length / 2) ≤ indexMetadataWordWidth buffer pos length := by
      unfold indexMetadataWordWidth
      exact binaryWordWidth_mono (by omega)
    have hHighWidth : indexMetadataWordWidth buffer (pos + length / 2) (length - length / 2) =
        indexMetadataWordWidth buffer pos length := by
      unfold indexMetadataWordWidth
      congr 1
      omega
    have hLowBound := hLow.trans (Nat.mul_le_mul_left (metadataNodeCount (length / 2))
      (Nat.add_le_add_right (Nat.mul_le_mul_left (12 + 6 * c) hLowWidth) 8))
    rw [hHighWidth] at hHigh
    rw [metadataNodeCount, ite_eq_right hLarge]
    nlinarith
termination_by length
decreasing_by all_goals omega

theorem indexMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (buffer : Array Bool) (pos length : ℕ) :
    indexMetadataBitWork primitive buffer pos length ≤
      (2 * length + 1) * ((12 + 6 * c) * indexMetadataWordWidth buffer pos length + 8) := by
  have hNodes : metadataNodeCount length ≤ 2 * length + 1 := by
    rw [metadataNodeCount_eq]
    split <;> omega
  exact (indexMetadataBitWork_node_bound primitive c hPrimitive buffer pos length).trans (Nat.mul_le_mul_right _ hNodes)

end Blotto.BinaryPayload
