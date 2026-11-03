import Blotto.BinaryRationalNormalization
import Blotto.RationalCostModel

/-! A separate cubic majorant accommodates the actually verified Boolean
normalizer. It does not realize the existing quadratic profile or the source
fast-Rat FPTAS headline. Arithmetic instruction/encoding joins remain open. -/

namespace Blotto
namespace RationalCostModel

def booleanCubic : RationalCostModel where
  rat := fun w => 150 * (w ^ 3 + w ^ 2 + w)
  monotone := by
    intro a b h
    have h2 := Nat.pow_le_pow_left h 2
    have h3 := Nat.pow_le_pow_left h 3
    exact Nat.mul_le_mul_left 150 (Nat.add_le_add (Nat.add_le_add h3 h2) h)
  word_le := by intro w; nlinarith
  superadditive := by intro a b; nlinarith

end RationalCostModel
namespace BinaryRationalNormalization

def encodingWidth (word : SignedWord) : ℕ := word.numerator.length + word.denominator.length + 1

theorem normalizeWithWork_cubic_price (word : SignedWord) :
    (normalizeWithWork word).2 ≤ RationalCostModel.booleanCubic.rat (encodingWidth word) := by
  have h := normalizeWithWork_bound word
  have hWidth : width word + 1 ≤ encodingWidth word := by unfold width encodingWidth; omega
  have hCube := Nat.pow_le_pow_left hWidth 3
  change _ ≤ 150 * (encodingWidth word ^ 3 + encodingWidth word ^ 2 + encodingWidth word)
  nlinarith

end BinaryRationalNormalization
end Blotto
