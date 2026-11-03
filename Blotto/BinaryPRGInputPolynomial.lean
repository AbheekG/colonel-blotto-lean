import Blotto.BinaryDecodedInputLength

/-! Incoming Boolean length alone bounds the joined canonical frame,
promise-checking and numerical-preparation ledger by an explicit quartic.
The statements cover malformed and promise-rejected frames. This component
ledger excludes numeric dimension/accuracy/seed/controller/physical costs;
it is not a complete machine runtime or storage theorem. -/

namespace Blotto.BinaryPRGInputPolynomial
open BinaryDecodedInputLength

theorem canonicalFrame_bound (length : ℕ) :
    BinaryCanonicalFrameWork.bound length ≤ 173 * (length + 1) ^ 3 := by
  have hp := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  unfold BinaryCanonicalFrameWork.bound
  nlinarith

theorem normalizedFrame_bound (length : ℕ) :
    BinaryPRGNormalizedFrameWork.bound length ≤ 531 * (length + 1) ^ 4 := by
  have hb := canonicalFrame_bound length
  have hp := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  have hh : 11 * length + 12 ≤ 12 * (length + 1) ^ 4 := by nlinarith
  have hc : (2 + (length + 1)) * BinaryCanonicalFrameWork.bound length ≤
      (3 * (length + 1)) * (173 * (length + 1) ^ 3) :=
    Nat.mul_le_mul (by omega) hb
  calc
    _ = 11 * length + 12 + (2 + (length + 1)) * BinaryCanonicalFrameWork.bound length := by
      unfold BinaryPRGNormalizedFrameWork.bound BinaryPRGNormalizedFrameWork.canonicalBound BinaryCanonicalRowReadWork.bound
      ring
    _ ≤ 12 * (length + 1) ^ 4 + (3 * (length + 1)) * (173 * (length + 1) ^ 3) := Nat.add_le_add hh hc
    _ = _ := by ring

theorem preparationFrame_bound (length : ℕ) :
    preparationFrameBound length ≤ 8614754500 * (length + 1) ^ 4 := by
  have hp := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 3 ≤ 4)
  unfold preparationFrameBound preparationEnvelope widthBound BinaryPRGPromiseWork.operationPrice BinaryPRGPromiseWork.comparisonPrice
  calc
    _ ≤ (2 * (length + 1)) * (12000 * (71 * (length + 1)) ^ 3) +
        (5 * (length + 1)) * (500 * (71 * (length + 1)) ^ 2) +
        (2 * (length + 1)) * (12000 * (8 * (length + 1)) ^ 3) := by
      gcongr <;> omega
    _ = 8602152000 * (length + 1) ^ 4 + 12602500 * (length + 1) ^ 3 := by ring
    _ ≤ 8602152000 * (length + 1) ^ 4 + 12602500 * (length + 1) ^ 4 := by gcongr
    _ = _ := by ring

def bound (length : ℕ) : ℕ := 8614755031 * (length + 1) ^ 4

theorem bound_mono {a b : ℕ} (h : a ≤ b) : bound a ≤ bound b := by
  unfold bound
  gcongr

theorem requestInputBound_le (length : ℕ) : requestInputBound length ≤ bound length := by
  unfold requestInputBound bound
  calc
    _ ≤ 531 * (length + 1) ^ 4 + 8614754500 * (length + 1) ^ 4 :=
      Nat.add_le_add (normalizedFrame_bound length) (preparationFrame_bound length)
    _ = _ := by ring

theorem read_bound (frame : List Bool) :
    (BinaryPRGNormalizedRequest.read frame).2.recorded ≤ bound frame.length :=
  (read_request_input_bound frame).trans (requestInputBound_le frame.length)

theorem run_bound (rich : Bool) (frame seed : List Bool) :
    (BinaryPRGNormalizedRequest.run rich frame seed).2.recorded ≤ bound frame.length :=
  (run_request_input_bound rich frame seed).trans (requestInputBound_le frame.length)

end Blotto.BinaryPRGInputPolynomial
