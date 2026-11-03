import Blotto.BinaryNatFrameDecodingCost
import Blotto.BinaryRatFrame
import Blotto.RationalExpressionBitCost

/-! Rational-frame parsing prices both numeric natural frames, the zero-
denominator rejection, signed conversion/division and reduced output words.
All input frames, including malformed ones, have polynomial labelled bounds. -/

namespace Blotto.BinaryRatFrame

theorem signedValue_wordWidth (negative : Bool) (magnitude : ℕ) :
    rationalWordWidth (signedValue negative magnitude) = binaryWordWidth magnitude + 2 := by
  cases negative <;> simp [signedValue, rationalWordWidth]
  all_goals
    have hOne : binaryWordWidth 1 = 1 := by decide
    rw [hOne]
    omega

def decodingBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) : List Bool → ℕ
  | [] => 1
  | negative :: bits =>
    1 + BinaryNatFrame.decodingBitWork primitive bits +
      match BinaryNatFrame.read bits with
      | none => 0
      | some first =>
        BinaryNatFrame.decodingBitWork primitive first.2 +
          match BinaryNatFrame.read first.2 with
          | none => 0
          | some second =>
            primitive (binaryWordWidth second.1) +
              if second.1 = 0 then 0 else
                4 * model.rat (RationalExpression.pairWidth (signedValue negative first.1) (second.1 : ℚ)) +
                  rationalWordWidth (signedValue negative first.1 / second.1)

theorem decodingBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    decodingBitWork model primitive frame ≤
      (10 * c + 30) * (frame.length + 2) ^ 2 + 5 * model.rat (4 * frame.length + 13) := by
  cases frame with
  | nil => simp only [decodingBitWork, List.length_nil]; nlinarith
  | cons negative bits =>
    let F := (negative :: bits).length
    let Q := (4 * c + 12) * (F + 2) ^ 2
    let P := model.rat (4 * F + 13)
    have hFirst : BinaryNatFrame.decodingBitWork primitive bits ≤ Q :=
      (BinaryNatFrame.decodingBitWork_bound primitive c hPrimitive bits).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [F]; simp) 2))
    simp only [decodingBitWork]
    cases hOne : BinaryNatFrame.read bits with
    | none =>
      simp only
      dsimp [Q, F] at hFirst
      simp only [List.length_cons]
      have hSquare : 1 ≤ (bits.length + 3) ^ 2 :=
        (by norm_num : 1 ≤ (3 : ℕ) ^ 2).trans (Nat.pow_le_pow_left (by omega) 2)
      have hCoefficient := Nat.mul_le_mul_right ((bits.length + 3) ^ 2)
        (show 4 * c + 13 ≤ 10 * c + 30 by omega)
      nlinarith
    | some first =>
      rcases first with ⟨magnitude, tail⟩
      have hTail := BinaryNatFrame.read_suffix_length bits magnitude tail hOne
      have hM := BinaryNatFrame.read_value_wordWidth bits magnitude tail hOne
      have hSecond : BinaryNatFrame.decodingBitWork primitive tail ≤ Q :=
        (BinaryNatFrame.decodingBitWork_bound primitive c hPrimitive tail).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [F]; omega) 2))
      simp only
      cases hTwo : BinaryNatFrame.read tail with
      | none =>
        simp only
        dsimp [Q, F] at hFirst hSecond
        simp only [List.length_cons]
        nlinarith
      | some second =>
        rcases second with ⟨denominator, suffix⟩
        have hD := BinaryNatFrame.read_value_wordWidth tail denominator suffix hTwo
        have hZero := (hPrimitive (binaryWordWidth denominator)).trans
          (Nat.mul_le_mul_left c (show binaryWordWidth denominator ≤ F + 1 by dsimp [F]; omega))
        have hSigned : rationalWordWidth (signedValue negative magnitude) ≤ F + 3 := by
          rw [signedValue_wordWidth]
          dsimp [F]
          omega
        have hDen : rationalWordWidth (denominator : ℚ) ≤ F + 3 := by
          have hdw := signedValue_wordWidth false denominator
          simp only [signedValue, Bool.false_eq_true, ite_false] at hdw
          rw [hdw]
          dsimp [F]
          omega
        have hPrice : model.rat (RationalExpression.pairWidth (signedValue negative magnitude) (denominator : ℚ)) ≤ P :=
          model.monotone (show RationalExpression.pairWidth _ _ ≤ 4 * F + 13 by
            unfold RationalExpression.pairWidth
            omega)
        have hResult := rationalWordWidth_of_height
          ((rationalHeight_of_wordWidth (signedValue negative magnitude)).div (rationalHeight_of_wordWidth (denominator : ℚ)))
        have hOut : rationalWordWidth (signedValue negative magnitude / denominator) ≤ P :=
          (hResult.trans (show 1 + 2 * (rationalWordWidth (signedValue negative magnitude) +
            rationalWordWidth (denominator : ℚ)) ≤ 4 * F + 13 by omega)).trans (model.word_le _)
        simp only
        change _ ≤ (10 * c + 30) * (F + 2) ^ 2 + 5 * P
        split <;> dsimp [Q] at hFirst hSecond <;> nlinarith

theorem read_suffix_lt (frame : List Bool) (q : ℚ) (suffix : List Bool)
    (h : read frame = some (q, suffix)) : suffix.length < frame.length := by
  cases frame with
  | nil => cases h
  | cons negative bits =>
    simp only [read] at h
    cases hOne : BinaryNatFrame.read bits with
    | none => rw [hOne, Option.bind_none] at h; cases h
    | some first =>
      rcases first with ⟨magnitude, tail⟩
      rw [hOne, Option.bind_some] at h
      cases hTwo : BinaryNatFrame.read tail with
      | none => rw [hTwo, Option.bind_none] at h; cases h
      | some second =>
        rcases second with ⟨denominator, rest⟩
        rw [hTwo, Option.bind_some] at h
        split at h
        · cases h
        · cases Option.some.inj h
          have hFirst := BinaryNatFrame.read_suffix_length bits magnitude tail hOne
          have hSecond := BinaryNatFrame.read_suffix_length tail denominator rest hTwo
          simp only [List.length_cons]
          omega

theorem read_suffix_length (frame : List Bool) (q : ℚ) (suffix : List Bool)
    (h : read frame = some (q, suffix)) : suffix.length ≤ frame.length :=
  (read_suffix_lt frame q suffix h).le

end Blotto.BinaryRatFrame
