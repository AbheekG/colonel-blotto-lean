import Blotto.GeneralPaperFirstOriginalSamplingContract
import Blotto.GeneralPaperOriginalDrawParameters

/-! Original-unit equal draw rates for the actual corrected midpoint and
stored representation. No accuracy encoding length enters these scales. -/
namespace Blotto.GeneralPaperFirstOriginalDrawParameters
open GeneralPaperOriginalGameInput GeneralPaperOriginalDrawParameters
open GeneralPaperSamplingOperandEnvelope (word_add)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem equal_size (model : RationalCostModel) (p : Input) :
    GeneralPaperEqualBitDrawRates.size p.n ((equalInput model p).k+1) (rationalWordWidth p.budget) ≤
      2 * originalSize p * logarithm p := by
  have hk := equal_exponent model p
  have hn := binaryWordWidth_mono (show p.n ≤ p.n + 4 by omega)
  have hb : rationalWordWidth p.budget ≤ originalSize p := by
    unfold originalSize GeneralPaperOneFieldBitOutput.originalSize; omega
  have hi := original_positive p
  have hl := log_positive p
  have hs : GeneralPaperEqualBitDrawRates.size p.n ((equalInput model p).k+1) (rationalWordWidth p.budget) ≤
      originalSize p + logarithm p := by unfold GeneralPaperEqualBitDrawRates.size logarithm; omega
  have hiL := Nat.mul_le_mul_right (logarithm p) hi
  have hLi := Nat.mul_le_mul_left (originalSize p) hl
  nlinarith only [hs, hiL, hLi]

theorem equal_scale (model : RationalCostModel) (p : Input) :
    GeneralPaperFirstStoredDrawRates.inputScale (equalInput model p) ≤
      4 * baseScale p * logarithm p := by
  have hn : p.n + 1 ≤ 2 * p.n := by have h := fields_positive p; omega
  have hm := Nat.mul_le_mul hn (equal_size model p)
  change (p.n + 1) * GeneralPaperEqualBitDrawRates.size p.n ((equalInput model p).k+1)
    (rationalWordWidth p.budget) ≤ _ at hm
  exact hm.trans_eq (by unfold baseScale; ring)

theorem equal_log (model : RationalCostModel) (p : Input) :
    GeneralPaperFirstStoredDrawRates.drawLog (equalInput model p) ≤ 4 * logarithm p := by
  let b := rationalWordWidth p.budget
  let k := (equalInput model p).k+1
  let s := GeneralPaperEqualBitDrawRates.size p.n k b
  have hk := equal_exponent model p
  have hn := binaryWordWidth_mono (show p.n ≤ p.n + 4 by omega)
  have hb : b ≤ originalSize p + 1 := by
    unfold b originalSize GeneralPaperOneFieldBitOutput.originalSize; omega
  have hbW := binaryWordWidth_mono hb
  have hnW := GeneralPaperSamplingFastBitBound.word_self (binaryWordWidth p.n)
  have hkW := GeneralPaperSamplingFastBitBound.word_self k
  have hs0 := word_add (b + binaryWordWidth p.n + k) 10
  have hs1 := word_add (b + binaryWordWidth p.n) k
  have hs2 := word_add b (binaryWordWidth p.n)
  have hP := binaryWordWidth_mul 67108864 s
  have h0 := word_add (p.n + 67108864 * s) 32
  have h1 := word_add p.n (67108864 * s)
  have h10 : binaryWordWidth 10 = 4 := by decide
  have h32 : binaryWordWidth 32 = 6 := by decide
  have hCoeff : binaryWordWidth 67108864 = 27 := by decide
  change binaryWordWidth s ≤ _ at hs0
  change binaryWordWidth (p.n + 67108864 * s + 32) + 1 ≤ _
  unfold logarithm
  dsimp only [b, k] at *
  omega


end Blotto.GeneralPaperFirstOriginalDrawParameters
