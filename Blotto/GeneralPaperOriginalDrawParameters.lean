import Blotto.GeneralPaperOriginalSamplingContract

/-! Final draw scales depend on the original rational game and the value of
accuracy, never its encoding length. All are erased observers of retained
input and existing accuracy provenance. -/
namespace Blotto.GeneralPaperOriginalDrawParameters
open GeneralPaperOriginalGameInput
open GeneralPaperSamplingOperandEnvelope (word_add)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def originalSize (p : Input) : ℕ := GeneralPaperOneFieldBitOutput.originalSize p

def logarithm (p : Input) : ℕ := 129 + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ +
  binaryWordWidth (p.n + 4) + binaryWordWidth (originalSize p + 1)

def baseScale (p : Input) : ℕ := p.n * originalSize p

def drawScale (p : Input) : ℚ := (p.n : ℚ) * ((originalSize p : ℚ) +
  GeneralPaperOriginalHeadlineParameters.nStar p / epsilon p)

def realScale (p : Input) : ℕ := p.n + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊

theorem original_positive (p : Input) : 1 ≤ originalSize p := by
  unfold originalSize GeneralPaperOneFieldBitOutput.originalSize
  omega

theorem log_positive (p : Input) : 1 ≤ logarithm p := by unfold logarithm; omega

theorem base_positive (p : Input) : 1 ≤ baseScale p :=
  Nat.mul_pos (fields_positive p) (original_positive p)

theorem base_le_scale (p : Input) : (baseScale p : ℚ) ≤ drawScale p := by
  have he := epsilon_positive p
  have hn := GeneralPaperOriginalHeadlineParameters.nstar_nonnegative p
  have h : 0 ≤ GeneralPaperOriginalHeadlineParameters.nStar p / epsilon p := by positivity
  unfold baseScale drawScale
  push_cast
  nlinarith only [h, Nat.cast_nonneg (α := ℚ) p.n]

theorem scale_positive (p : Input) : (1 : ℚ) ≤ drawScale p := by
  have h : (1 : ℚ) ≤ baseScale p := by exact_mod_cast base_positive p
  exact h.trans (base_le_scale p)

theorem equal_exponent (model : RationalCostModel) (p : Input) :
    (equalInput model p).k ≤ binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ := by
  rw [GeneralPaperEqualInputHeadline.exponent_exact]
  exact GeneralPaperRealHeadlineParameters.exponent_bound (epsilon p)

theorem equal_size (model : RationalCostModel) (p : Input) :
    GeneralPaperEqualBitDrawRates.size p.n (equalInput model p).k (rationalWordWidth p.budget) ≤
      2 * originalSize p * logarithm p := by
  have hk := equal_exponent model p
  have hn := binaryWordWidth_mono (show p.n ≤ p.n + 4 by omega)
  have hb : rationalWordWidth p.budget ≤ originalSize p := by
    unfold originalSize GeneralPaperOneFieldBitOutput.originalSize; omega
  have hi := original_positive p
  have hl := log_positive p
  have hs : GeneralPaperEqualBitDrawRates.size p.n (equalInput model p).k (rationalWordWidth p.budget) ≤
      originalSize p + logarithm p := by unfold GeneralPaperEqualBitDrawRates.size logarithm; omega
  have hiL := Nat.mul_le_mul_right (logarithm p) hi
  have hLi := Nat.mul_le_mul_left (originalSize p) hl
  nlinarith only [hs, hiL, hLi]

theorem equal_scale (model : RationalCostModel) (p : Input) :
    GeneralPaperStoredSelectedReturnWork.inputScale (equalInput model p) ≤
      4 * baseScale p * logarithm p := by
  have hn : p.n + 1 ≤ 2 * p.n := by have h := fields_positive p; omega
  have hm := Nat.mul_le_mul hn (equal_size model p)
  change (p.n + 1) * GeneralPaperEqualBitDrawRates.size p.n (equalInput model p).k
    (rationalWordWidth p.budget) ≤ _ at hm
  exact hm.trans_eq (by unfold baseScale; ring)

theorem equal_log (model : RationalCostModel) (p : Input) :
    GeneralPaperStoredNativeReadRates.drawLog (equalInput model p) ≤ 4 * logarithm p := by
  let b := rationalWordWidth p.budget
  let k := (equalInput model p).k
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

theorem native_log (p : Input) (hStrict : p.budget < 1) :
    GeneralPaperNativeDrawHeadline.drawLog (unequalInput p hStrict) ≤ logarithm p := by
  have hb : GeneralPaperNativeResourceDomain.originalInputSize (unequalInput p hStrict) + 1 ≤ originalSize p + 1 := by
    unfold GeneralPaperNativeResourceDomain.originalInputSize GeneralPaperNativeResourceDomain.originalSize
      unequalInput originalSize GeneralPaperOneFieldBitOutput.originalSize
    dsimp only
    omega
  have hw := binaryWordWidth_mono hb
  change 128 + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + binaryWordWidth (p.n + 4) +
    binaryWordWidth (GeneralPaperNativeResourceDomain.originalInputSize (unequalInput p hStrict) + 1) ≤ _
  unfold logarithm
  omega

theorem native_scale (p : Input) (hStrict : p.budget < 1) :
    GeneralPaperNativeDrawHeadline.drawScale (unequalInput p hStrict) ≤ drawScale p := by
  have hb : GeneralPaperNativeResourceDomain.originalInputSize (unequalInput p hStrict) ≤ originalSize p := by
    unfold GeneralPaperNativeResourceDomain.originalInputSize GeneralPaperNativeResourceDomain.originalSize
      unequalInput originalSize GeneralPaperOneFieldBitOutput.originalSize
    dsimp only
    omega
  have hQ : (GeneralPaperNativeResourceDomain.originalInputSize (unequalInput p hStrict) : ℚ) ≤ originalSize p := by
    exact_mod_cast hb
  change (p.n : ℚ) * ((_ : ℚ) + GeneralPaperOriginalHeadlineParameters.nStar p / epsilon p) ≤ _
  unfold drawScale
  gcongr

end Blotto.GeneralPaperOriginalDrawParameters
