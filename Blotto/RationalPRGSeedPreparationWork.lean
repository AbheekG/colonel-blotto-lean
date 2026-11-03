import Blotto.RationalPRGBinaryRequest
import Blotto.BinaryListLengthWork

/-! Exact seed-length checking prices the complete length counter and one
natural equality test. Successful table preparation reads/writes each seed bit;
failed checks build no table. Addressing/ownership/backend remain separate. -/

namespace Blotto.RationalPRGBinaryRequest

def seedPreparationBitWork (primitive : ℕ → ℕ) (count : ℕ) (seed : List Bool) : ℕ :=
  listLengthBitWork primitive 0 seed + primitive (max (binaryWordWidth seed.length) (binaryWordWidth count)) +
    if seed.length = count then 2 * seed.length else 0

theorem seedPreparationBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (seed : List Bool) :
    seedPreparationBitWork primitive count seed ≤
      (seed.length + 1) * ((c + 2) * binaryWordWidth (seed.length + 1) + 1) +
        c * max (binaryWordWidth seed.length) (binaryWordWidth count) + 2 * seed.length := by
  have hLength := listLengthBitWork_bound primitive c hPrimitive 0 seed
  simp only [Nat.zero_add] at hLength
  have hCompare := hPrimitive (max (binaryWordWidth seed.length) (binaryWordWidth count))
  unfold seedPreparationBitWork
  split <;> omega

theorem seedPreparationBitWork_wrong_length (primitive : ℕ → ℕ) (count : ℕ) (seed : List Bool)
    (h : seed.length ≠ count) :
    seedPreparationBitWork primitive count seed = listLengthBitWork primitive 0 seed +
      primitive (max (binaryWordWidth seed.length) (binaryWordWidth count)) := by
  simp only [seedPreparationBitWork, ite_eq_right h, Nat.add_zero]

end Blotto.RationalPRGBinaryRequest
