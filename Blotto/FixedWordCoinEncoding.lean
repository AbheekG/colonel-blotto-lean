import Blotto.FixedWordCoinRefinement

/-! Native normalized numerator/denominator words are encoded once before
Boolean coin execution. The whole result and consumed count match the old API.
Encoder backend costs are separate from the fixed-width Boolean loop. -/

namespace Blotto.FixedWordCoin

def encoded (K a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (bits : Fin K → Bool) : Option Bool × ℕ :=
  let w := binaryWordWidth b
  let numerator := FixedBinaryWord.ofNat w a
  let denominator := FixedBinaryWord.ofNat w b
  have hB := FixedBinaryWord.value_ofNat w b (lt_pow_binaryWordWidth b)
  have hA := FixedBinaryWord.value_ofNat w a (hab.trans_lt (lt_pow_binaryWordWidth b))
  run K numerator denominator (by rw [hB]; exact hb) (by rw [hA, hB]; exact hab) bits

theorem encoded_refines (K a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (bits : Fin K → Bool) :
    encoded K a b hb hab bits = runFixedDenominatorCoin K a b bits := by
  unfold encoded
  rw [run_refines]
  rw [FixedBinaryWord.value_ofNat _ b (lt_pow_binaryWordWidth b),
    FixedBinaryWord.value_ofNat _ a (hab.trans_lt (lt_pow_binaryWordWidth b))]

end Blotto.FixedWordCoin
