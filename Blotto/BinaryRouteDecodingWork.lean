import Blotto.BinaryRouteFrame
import Blotto.BinaryRatFrameDecodingCost

/-! Actual route decoding includes tag dispatch, optional natural-index
parsing/validation and signed rational parsing. Bounds cover malformed frames;
natural/rational primitive realization remains an explicit model parameter. -/

namespace Blotto.BinaryRouteFrame

def decodingWork (model : RationalCostModel) (primitive : ℕ → ℕ) (m : ℕ) : List Bool → ℕ
  | [] => 1
  | false :: rest => 1 + BinaryRatFrame.decodingBitWork model primitive rest
  | true :: rest => 1 + BinaryNatFrame.decodingBitWork primitive rest +
      match BinaryNatFrame.read rest with
      | none => 0
      | some parsed =>
          binaryWordWidth parsed.1 + binaryWordWidth m +
            primitive (max (binaryWordWidth parsed.1) (binaryWordWidth m)) +
              if parsed.1 < m then BinaryRatFrame.decodingBitWork model primitive parsed.2 else 0

def decodingBound (model : RationalCostModel) (c m length : ℕ) : ℕ :=
  (14 * c + 43) * (length + 2) ^ 2 + (1 + c) * (length + 1 + binaryWordWidth m) +
    5 * model.rat (4 * length + 13)

theorem decodingWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (m : ℕ) (frame : List Bool) :
    decodingWork model primitive m frame ≤ decodingBound model c m frame.length := by
  cases frame with
  | nil => unfold decodingWork decodingBound; simp only [List.length_nil]; nlinarith
  | cons tag rest =>
    let F := (tag :: rest).length
    have hNat : BinaryNatFrame.decodingBitWork primitive rest ≤ (4 * c + 12) * (F + 2) ^ 2 :=
      (BinaryNatFrame.decodingBitWork_bound primitive c hPrimitive rest).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [F]; simp) 2))
    have hRat : ∀ tail : List Bool, tail.length ≤ rest.length →
        BinaryRatFrame.decodingBitWork model primitive tail ≤
          (10 * c + 30) * (F + 2) ^ 2 + 5 * model.rat (4 * F + 13) := by
      intro tail hTail
      exact (BinaryRatFrame.decodingBitWork_bound model primitive c hPrimitive tail).trans
        (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simp only [F, List.length_cons]; omega) 2))
          (Nat.mul_le_mul_left 5 (model.monotone (by simp only [F, List.length_cons]; omega))))
    cases tag with
    | false =>
      have hr := hRat rest le_rfl
      change 1 + BinaryRatFrame.decodingBitWork model primitive rest ≤ decodingBound model c m (false :: rest).length
      unfold decodingBound
      dsimp [F] at hr
      simp only [List.length_cons]
      nlinarith
    | true =>
      change 1 + BinaryNatFrame.decodingBitWork primitive rest +
        (match BinaryNatFrame.read rest with
        | none => 0
        | some parsed => binaryWordWidth parsed.1 + binaryWordWidth m +
            primitive (max (binaryWordWidth parsed.1) (binaryWordWidth m)) +
              if parsed.1 < m then BinaryRatFrame.decodingBitWork model primitive parsed.2 else 0) ≤ _
      cases hParsed : BinaryNatFrame.read rest with
      | none =>
        dsimp only
        unfold decodingBound
        dsimp [F] at hNat
        simp only [List.length_cons]
        nlinarith
      | some parsed =>
        rcases parsed with ⟨index, tail⟩
        have hTail := BinaryNatFrame.read_suffix_length rest index tail hParsed
        have hIndex := BinaryNatFrame.read_value_wordWidth rest index tail hParsed
        have hPrice := (hPrimitive (max (binaryWordWidth index) (binaryWordWidth m))).trans
          (Nat.mul_le_mul_left c (show max (binaryWordWidth index) (binaryWordWidth m) ≤ F + 1 + binaryWordWidth m by simp only [F, List.length_cons]; omega))
        have hr := hRat tail hTail
        dsimp only
        unfold decodingBound
        split <;> dsimp [F] at hNat hPrice hr <;> simp only [List.length_cons] <;> nlinarith

end Blotto.BinaryRouteFrame
