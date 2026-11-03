import Blotto.GeneralPaperPrecallCachePrice
import Blotto.GeneralPaperInitializerControlCounters

/-! Short widths of every reached power-constructor return counter.
Natural powers and scales are arithmetic operands priced separately.
Their step/work counters require only the logarithm of the logarithm of
the constructed scale; linear dyadic construction uses the exponent width.
The caller's final simultaneous word/capacity join remains separate.
-/
namespace Blotto.GeneralPaperParameterCounterWords
set_option autoImplicit false

theorem linear_word (n : ℕ) : binaryWordWidth (12*n+194)≤binaryWordWidth n+14 := by
  have hm := binaryWordWidth_mul 12 n
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (12*n) 194
  have h12 : binaryWordWidth 12=4 := by decide
  have h194 : binaryWordWidth 194=8 := by decide
  omega

theorem ceiling (primitive : ℕ → ℕ) (W target p : ℕ) (hp : 0<p)
    (hW : binaryWordWidth (binaryWordWidth target+1)+32≤W) :
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive W target p hp).1.doublings+1)≤W ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive W target p hp).1.work+192)≤W := by
  rw [GeneralPaperPowerCeilingBits.loop_data]
  have hd := GeneralPaperPowerCeiling.loop_depth target p hp
  have hw := (GeneralPaperPowerCeiling.loop_spec target p hp).2.2.2.2
  have hs := binaryWordWidth_mono (Nat.add_le_add_right hd 1)
  have hBound : (GeneralPaperPowerCeiling.loop target p hp).work+192≤12*binaryWordWidth target+194 := by omega
  have hb := binaryWordWidth_mono hBound
  have hl := linear_word (binaryWordWidth target)
  have hm := binaryWordWidth_mono (show binaryWordWidth target≤binaryWordWidth target+1 by omega)
  exact ⟨by omega,by omega⟩

theorem power (primitive : ℕ → ℕ) (W base exponent : ℕ)
    (hW : binaryWordWidth (binaryWordWidth exponent+1)+32≤W) :
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive W base exponent).1.steps+1)≤W ∧
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive W base exponent).1.work+12)≤W := by
  rw [GeneralPaperNatPowerBits.data]
  have hd := GeneralPaperNatPower.steps_le base exponent (binaryWordWidth exponent) (lt_pow_binaryWordWidth exponent)
  have hw := (GeneralPaperNatPower.data base exponent).2
  have hs := binaryWordWidth_mono (Nat.add_le_add_right hd 1)
  have hBound : (GeneralPaperNatPower.run base exponent).work+12≤12*binaryWordWidth exponent+194 := by omega
  have hb := binaryWordWidth_mono hBound
  have hl := linear_word (binaryWordWidth exponent)
  have hm := binaryWordWidth_mono (show binaryWordWidth exponent≤binaryWordWidth exponent+1 by omega)
  exact ⟨by omega,by omega⟩

theorem power_prefix (primitive : ℕ → ℕ) (W base outer exponent : ℕ) (he : exponent≤outer)
    (hW : binaryWordWidth (binaryWordWidth outer+1)+32≤W) :
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive W base exponent).1.steps+1)≤W ∧
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive W base exponent).1.work+12)≤W := by
  apply power
  have hi := binaryWordWidth_mono he
  have ho := binaryWordWidth_mono (Nat.add_le_add_right hi 1)
  omega

theorem dyadic (primitive : ℕ → ℕ) (W exponent : ℕ)
    (hW : binaryWordWidth (exponent+1)+32≤W) :
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive W exponent).1.doublings+1)≤W ∧
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive W exponent).1.work+8)≤W := by
  rw [GeneralPaperDyadicPowerBits.data]
  have hd := (GeneralPaperScoreScaleParameters.power_data exponent).2.1
  have hw := (GeneralPaperScoreScaleParameters.power_data exponent).2.2
  have hs : binaryWordWidth ((GeneralPaperScoreScaleParameters.powerRun exponent).doublings+1)=binaryWordWidth (exponent+1) := by rw [hd]
  have hBound : (GeneralPaperScoreScaleParameters.powerRun exponent).work+8≤12*(exponent+1)+194 := by omega
  have hb := binaryWordWidth_mono hBound
  have hl := linear_word (exponent+1)
  exact ⟨by omega,by omega⟩

theorem dyadic_prefix (primitive : ℕ → ℕ) (W outer exponent : ℕ) (he : exponent≤outer)
    (hW : binaryWordWidth (outer+1)+32≤W) :
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive W exponent).1.doublings+1)≤W ∧
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive W exponent).1.work+8)≤W := by
  apply dyadic
  have hi := binaryWordWidth_mono (Nat.add_le_add_right he 1)
  omega

end Blotto.GeneralPaperParameterCounterWords
