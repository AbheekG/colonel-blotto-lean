import Blotto.BinaryPayloadMergeBitWork
import Blotto.BinaryWordParseBounds

/-! Prices the existing numeric natural-frame reader, including its width
counter, full suffix-length pass, truncation gate and balanced payload decoder.
Bounds include malformed frames. Natural primitive realization and physical
allocation/addressing remain explicit external interpretation contracts. -/

namespace Blotto.BinaryNatFrame

def scanBitWork (primitive : ℕ → ℕ) : ℕ → List Bool → ℕ
  | _, [] => 1
  | _, true :: _ => 1
  | count, false :: rest =>
    binaryWordWidth count + binaryWordWidth (count + 1) +
      primitive (binaryWordWidth (count + 1)) + 1 + scanBitWork primitive (count + 1) rest

theorem scanBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (frame : List Bool) :
    scanBitWork primitive count frame ≤
      (frame.length + 1) * ((2 + c) * (count + frame.length + 1) + 1) := by
  induction frame generalizing count with
  | nil => simp [scanBitWork]
  | cons bit rest ih =>
    cases bit
    · have hCount : binaryWordWidth count ≤ count + rest.length + 2 := by
        have h := Nat.log2_le_self count
        unfold binaryWordWidth
        omega
      have hNext : binaryWordWidth (count + 1) ≤ count + rest.length + 2 := by
        have h := Nat.log2_le_self (count + 1)
        unfold binaryWordWidth
        omega
      have hp := (hPrimitive (binaryWordWidth (count + 1))).trans (Nat.mul_le_mul_left c hNext)
      have ht := ih (count + 1)
      simp only [scanBitWork, List.length_cons]
      nlinarith
    · simp only [scanBitWork, List.length_cons]
      exact Nat.succ_le_iff.mpr (Nat.mul_pos (by omega) (by omega))

def decodingBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  scanBitWork primitive 0 frame +
    match scanWidth 0 frame with
    | none => 0
    | some pair =>
      pair.2.length + primitive (max (binaryWordWidth pair.1) (binaryWordWidth pair.2.length)) +
        if pair.1 ≤ pair.2.length then
          3 * pair.1 + BinaryPayload.balancedBitWork primitive (pair.2.take pair.1).toArray 0 pair.1
        else 0

theorem decodingBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    decodingBitWork primitive frame ≤ (4 * c + 12) * (frame.length + 2) ^ 2 := by
  have hScan := scanBitWork_bound primitive c hPrimitive 0 frame
  simp only [Nat.zero_add] at hScan
  unfold decodingBitWork
  cases hRead : scanWidth 0 frame with
  | none => simp only [Nat.add_zero]; nlinarith
  | some pair =>
    rcases pair with ⟨width, rest⟩
    have hLength := scanWidth_length 0 frame width rest hRead
    simp only [Nat.zero_add] at hLength
    have hW : binaryWordWidth width ≤ frame.length + 1 := by
      have h := Nat.log2_le_self width
      unfold binaryWordWidth
      omega
    have hR : binaryWordWidth rest.length ≤ frame.length + 1 := by
      have h := Nat.log2_le_self rest.length
      unfold binaryWordWidth
      omega
    have hp := (hPrimitive (max (binaryWordWidth width) (binaryWordWidth rest.length))).trans
      (Nat.mul_le_mul_left c (max_le hW hR))
    have hPayload := BinaryPayload.balancedBitWork_word_bound primitive c hPrimitive
      (rest.take width).toArray 0 width
    have hMerge := Nat.mul_le_mul_left (4 + 2 * c)
      (Nat.mul_le_mul (show width ≤ frame.length by omega) hW)
    dsimp only
    split
    · nlinarith
    · nlinarith

theorem read_suffix_length (frame : List Bool) (n : ℕ) (suffix : List Bool)
    (h : read frame = some (n, suffix)) : suffix.length ≤ frame.length := by
  unfold read at h
  cases hs : scanWidth 0 frame with
  | none => rw [hs, Option.bind_none] at h; cases h
  | some pair =>
    rcases pair with ⟨width, rest⟩
    rw [hs, Option.bind_some] at h
    split at h
    · cases Option.some.inj h
      have hLength := scanWidth_length 0 frame width rest hs
      simp only [List.length_drop, Nat.zero_add] at hLength ⊢
      omega
    · cases h

theorem read_value_wordWidth (frame : List Bool) (n : ℕ) (suffix : List Bool)
    (h : read frame = some (n, suffix)) : binaryWordWidth n ≤ frame.length + 1 := by
  unfold read at h
  cases hs : scanWidth 0 frame with
  | none => rw [hs, Option.bind_none] at h; cases h
  | some pair =>
    rcases pair with ⟨width, rest⟩
    rw [hs, Option.bind_some] at h
    split at h
    · cases Option.some.inj h
      have hLength := scanWidth_length 0 frame width rest hs
      have hb := BinaryPayload.balancedValue_bounds (rest.take width).toArray 0 (rest.take width).length
      apply binaryWordWidth_le_of_lt_pow (by omega : 0 < frame.length + 1)
      exact hb.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by
        simp only [List.length_take, Nat.zero_add] at hLength ⊢
        omega))
    · cases h

end Blotto.BinaryNatFrame
