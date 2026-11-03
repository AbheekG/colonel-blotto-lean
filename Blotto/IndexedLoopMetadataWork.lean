import Blotto.BinaryListLengthWork

/-! Conservative index/control word allowance for a bounded ascending loop.
Each body/exit prices index/length/capacity words and three natural control
primitives. Iterator body payload work and physical addresses/records remain
separate. The current position and remaining count determine every word cap. -/

namespace Blotto

def indexedLoopMetadataBitWork (primitive : ℕ → ℕ) (pos : ℕ) : ℕ → ℕ
  | 0 => 6 * binaryWordWidth (pos + 0 + 1) + 3 * primitive (binaryWordWidth (pos + 0 + 1)) + 6
  | remaining + 1 =>
    6 * binaryWordWidth (pos + (remaining + 1) + 1) +
      3 * primitive (binaryWordWidth (pos + (remaining + 1) + 1)) + 6 + indexedLoopMetadataBitWork primitive (pos + 1) remaining

theorem indexedLoopMetadataBitWork_eq (primitive : ℕ → ℕ) (pos remaining : ℕ) :
    indexedLoopMetadataBitWork primitive pos remaining = (remaining + 1) *
      (6 * binaryWordWidth (pos + remaining + 1) + 3 * primitive (binaryWordWidth (pos + remaining + 1)) + 6) := by
  induction remaining generalizing pos with
  | zero => simp only [indexedLoopMetadataBitWork, Nat.zero_add, Nat.one_mul]
  | succ remaining ih =>
    rw [indexedLoopMetadataBitWork, ih]
    have hSame : pos + 1 + remaining + 1 = pos + (remaining + 1) + 1 := by omega
    rw [hSame]
    ring

def indexedLoopMetadataBound (c length : ℕ) : ℕ :=
  (length + 1) * ((6 + 3 * c) * binaryWordWidth (length + 1) + 6)

theorem indexedLoopMetadataBound_mono (c : ℕ) : Monotone (indexedLoopMetadataBound c) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 1)
  unfold indexedLoopMetadataBound
  gcongr

theorem indexedLoopMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (length : ℕ) :
    indexedLoopMetadataBitWork primitive 0 length ≤ indexedLoopMetadataBound c length := by
  have hp := hPrimitive (binaryWordWidth (length + 1))
  rw [indexedLoopMetadataBitWork_eq]
  simp only [Nat.zero_add]
  unfold indexedLoopMetadataBound
  gcongr
  nlinarith

end Blotto
