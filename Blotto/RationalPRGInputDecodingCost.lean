import Blotto.BinaryRatListDecodingCost
import Blotto.RationalPRGBinaryInput

/-! Prices the game frame's actual ordered parser calls and early failures.
The bound depends on the input frame length, not a decoded numeric dimension.
Promise recognition, count bookkeeping, table construction, metadata/address
and physical backend/ownership are separate. -/

namespace Blotto.RationalPRGBinaryInput

def decodingBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  BinaryNatFrame.decodingBitWork primitive frame +
    match BinaryNatFrame.read frame with
    | none => 0
    | some dim => BinaryRatFrame.decodingBitWork model primitive dim.2 +
      match BinaryRatFrame.read dim.2 with
      | none => 0
      | some first => BinaryRatFrame.decodingBitWork model primitive first.2 +
        match BinaryRatFrame.read first.2 with
        | none => 0
        | some second => BinaryRatListFrame.decodingBitWork model primitive dim.1 second.2

def decodingBound (model : RationalCostModel) (c length : ℕ) : ℕ :=
  (4 * c + 12) * (length + 2) ^ 2 +
    (length + 3) * (BinaryRatListFrame.decodingFramePrice model c length + 1)

theorem decodingBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (frame : List Bool) :
    decodingBitWork model primitive frame ≤ decodingBound model c frame.length := by
  let P := BinaryRatListFrame.decodingFramePrice model c frame.length
  have hNat := BinaryNatFrame.decodingBitWork_bound primitive c hPrimitive frame
  have hRat : ∀ tail : List Bool, tail.length ≤ frame.length →
      BinaryRatFrame.decodingBitWork model primitive tail ≤ P := by
    intro tail hTail
    exact (BinaryRatFrame.decodingBitWork_bound model primitive c hPrimitive tail).trans
      (BinaryRatListFrame.decodingFramePrice_mono model c hTail)
  have hRow : ∀ count : ℕ, ∀ tail : List Bool, tail.length ≤ frame.length →
      BinaryRatListFrame.decodingBitWork model primitive count tail ≤ (frame.length + 1) * (P + 1) := by
    intro count tail hTail
    exact (BinaryRatListFrame.decodingBitWork_bound model primitive c hPrimitive count tail).trans
      (Nat.mul_le_mul (Nat.add_le_add_right hTail 1)
        (Nat.add_le_add_right (BinaryRatListFrame.decodingFramePrice_mono model c hTail) 1))
  unfold decodingBitWork
  cases hDim : BinaryNatFrame.read frame with
  | none =>
    simp only
    unfold decodingBound
    omega
  | some dim =>
    rcases dim with ⟨count, tail⟩
    have hTail := BinaryNatFrame.read_suffix_length frame count tail hDim
    have hFirst := hRat tail hTail
    simp only
    cases hReadA : BinaryRatFrame.read tail with
    | none =>
      simp only
      change _ ≤ (4 * c + 12) * (frame.length + 2) ^ 2 + (frame.length + 3) * (P + 1)
      nlinarith
    | some first =>
      rcases first with ⟨a, rest⟩
      have hRest := (BinaryRatFrame.read_suffix_length tail a rest hReadA).trans hTail
      have hSecond := hRat rest hRest
      simp only
      cases hReadB : BinaryRatFrame.read rest with
      | none =>
        simp only
        change _ ≤ (4 * c + 12) * (frame.length + 2) ^ 2 + (frame.length + 3) * (P + 1)
        nlinarith
      | some second =>
        rcases second with ⟨b, remaining⟩
        have hRemaining := (BinaryRatFrame.read_suffix_length rest b remaining hReadB).trans hRest
        have hList := hRow count remaining hRemaining
        simp only
        change _ ≤ (4 * c + 12) * (frame.length + 2) ^ 2 + (frame.length + 3) * (P + 1)
        nlinarith

end Blotto.RationalPRGBinaryInput
