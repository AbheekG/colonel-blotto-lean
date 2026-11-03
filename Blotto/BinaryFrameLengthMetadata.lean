import Blotto.BinaryListLengthWork
import Blotto.BinaryRatListCounterWork

/-! Additional integer word work for the numeric readers' full suffix-length
passes. Existing traversal labels are retained, so the combined price is
conservative. Frame parsing and short-circuit row reads determine the calls;
decoder indices, addresses, records and physical ownership remain separate. -/

namespace Blotto.BinaryNatFrame

def lengthMetadataBitWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  match scanWidth 0 frame with
  | none => 0
  | some pair => listLengthBitWork primitive 0 pair.2

def lengthMetadataBound (c length : ℕ) : ℕ :=
  (length + 1) * ((c + 2) * binaryWordWidth (length + 1) + 1)

theorem lengthMetadataBound_mono (c : ℕ) : Monotone (lengthMetadataBound c) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 1)
  unfold lengthMetadataBound
  gcongr

theorem lengthMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    lengthMetadataBitWork primitive frame ≤ lengthMetadataBound c frame.length := by
  unfold lengthMetadataBitWork
  cases hScan : scanWidth 0 frame with
  | none => exact Nat.zero_le _
  | some pair =>
    rcases pair with ⟨width, rest⟩
    have hSize := scanWidth_length 0 frame width rest hScan
    have hRest : rest.length ≤ frame.length := by omega
    have hWork := listLengthBitWork_bound primitive c hPrimitive 0 rest
    simp only [Nat.zero_add] at hWork
    exact hWork.trans (lengthMetadataBound_mono c hRest)

end Blotto.BinaryNatFrame
namespace Blotto.BinaryRatFrame

def lengthMetadataBitWork (primitive : ℕ → ℕ) : List Bool → ℕ
  | [] => 0
  | _ :: bits => BinaryNatFrame.lengthMetadataBitWork primitive bits +
    match BinaryNatFrame.read bits with
    | none => 0
    | some first => BinaryNatFrame.lengthMetadataBitWork primitive first.2

theorem lengthMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    lengthMetadataBitWork primitive frame ≤ 2 * BinaryNatFrame.lengthMetadataBound c frame.length := by
  cases frame with
  | nil => exact Nat.zero_le _
  | cons negative bits =>
    have hFirst := BinaryNatFrame.lengthMetadataBitWork_bound primitive c hPrimitive bits
    have hFirstPrice := BinaryNatFrame.lengthMetadataBound_mono c (show bits.length ≤ (negative :: bits).length by simp)
    simp only [lengthMetadataBitWork]
    cases hRead : BinaryNatFrame.read bits with
    | none => simp only; omega
    | some first =>
      rcases first with ⟨n, suffix⟩
      have hSuffix := BinaryNatFrame.read_suffix_length bits n suffix hRead
      have hSecond := BinaryNatFrame.lengthMetadataBitWork_bound primitive c hPrimitive suffix
      have hSecondPrice := BinaryNatFrame.lengthMetadataBound_mono c
        (show suffix.length ≤ (negative :: bits).length by simp only [List.length_cons]; omega)
      simp only
      omega

end Blotto.BinaryRatFrame
namespace Blotto.BinaryRatListFrame

def lengthMetadataBitWork (primitive : ℕ → ℕ) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | count + 1, frame => BinaryRatFrame.lengthMetadataBitWork primitive frame +
    match BinaryRatFrame.read frame with
    | none => 0
    | some first => lengthMetadataBitWork primitive count first.2

theorem lengthMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (count : ℕ) (frame : List Bool) :
    lengthMetadataBitWork primitive count frame ≤
      2 * (frame.length + 1) * BinaryNatFrame.lengthMetadataBound c frame.length := by
  induction count generalizing frame with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    have hHead := BinaryRatFrame.lengthMetadataBitWork_bound primitive c hPrimitive frame
    simp only [lengthMetadataBitWork]
    cases hRead : BinaryRatFrame.read frame with
    | none =>
      simp only
      have hMul := Nat.mul_le_mul_right (BinaryNatFrame.lengthMetadataBound c frame.length)
        (show 2 ≤ 2 * (frame.length + 1) by omega)
      omega
    | some first =>
      rcases first with ⟨q, suffix⟩
      have hSuffix := BinaryRatFrame.read_suffix_lt frame q suffix hRead
      have hTail := ih suffix
      have hPrice := Nat.mul_le_mul_left (2 * (suffix.length + 1))
        (BinaryNatFrame.lengthMetadataBound_mono c hSuffix.le)
      have hCount := Nat.mul_le_mul_right (BinaryNatFrame.lengthMetadataBound c frame.length)
        (show 2 * (suffix.length + 2) ≤ 2 * (frame.length + 1) by omega)
      simp only
      nlinarith

end Blotto.BinaryRatListFrame
