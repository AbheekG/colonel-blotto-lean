import Blotto.GeneralPaperPrecallControlWord

/-! Discharge the actual constructor-loop counter capacities at one word.
Every reached dyadic exponent, halved power exponent and positive doubling
state is covered. No loop-depth or returned-counter size oracle is supplied.
-/
namespace Blotto.GeneralPaperPrecallLoopWords
open GeneralPaperPrecallControlWord
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem dyadic (primitive : ℕ → ℕ) (m k exponent : ℕ) (he : exponent≤17+k) :
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive (word m k) exponent).1.doublings+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive (word m k) exponent).1.work+8)≤word m k := by
  have ht := (terms m k).1
  have hw := measured m k (k+18) ht
  apply GeneralPaperParameterCounterWords.dyadic_prefix primitive (word m k) (17+k) exponent he
  have hEq : 17+k+1=k+18 := by omega
  rw [hEq]
  omega

theorem root_power (primitive : ℕ → ℕ) (m k exponent : ℕ)
    (he : exponent≤(GeneralPaperProxyParameters.prepare m k).d+2) :
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive (word m k) (m+3) exponent).1.steps+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive (word m k) (m+3) exponent).1.work+12)≤word m k := by
  have ht := (terms m k).2.2.1
  have hw := measured m k _ ht
  apply GeneralPaperParameterCounterWords.power_prefix primitive (word m k) (m+3)
    ((GeneralPaperProxyParameters.prepare m k).d+2) exponent he
  omega

theorem alphabet_power (primitive : ℕ → ℕ) (m k exponent : ℕ)
    (he : exponent≤(GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J) :
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive (word m k) (m+2) exponent).1.steps+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperNatPowerBits.run primitive (word m k) (m+2) exponent).1.work+12)≤word m k := by
  have ht := (terms m k).2.2.2.2.1
  have hw := measured m k _ ht
  apply GeneralPaperParameterCounterWords.power_prefix primitive (word m k) (m+2)
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J exponent he
  omega

theorem score_ceiling (primitive : ℕ → ℕ) (m k p : ℕ) (hp : 0<p) :
    let target := m*(GeneralPaperScoreScaleParameters.prepare m k).K
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k) target p hp).1.doublings+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k) target p hp).1.work+192)≤word m k := by
  have ht := (terms m k).2.1
  have hw := measured m k _ ht
  apply GeneralPaperParameterCounterWords.ceiling
  omega

theorem root_ceiling (primitive : ℕ → ℕ) (m k p : ℕ) (hp : 0<p) :
    let H := (GeneralPaperProxyParameters.prepare m k).H
    let target := 4*H*H
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k) target p hp).1.doublings+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k) target p hp).1.work+192)≤word m k := by
  have ht := (terms m k).2.2.2.1
  have hw := measured m k _ ht
  apply GeneralPaperParameterCounterWords.ceiling
  omega

theorem alphabet_ceiling (primitive : ℕ → ℕ) (m k p : ℕ) (hp : 0<p) :
    let D := (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).D
    let target := 4*D*D
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k) target p hp).1.doublings+1)≤word m k ∧
    binaryWordWidth ((GeneralPaperPowerCeilingBits.loop primitive (word m k) target p hp).1.work+192)≤word m k := by
  have ht := (terms m k).2.2.2.2.2.1
  have hw := measured m k _ ht
  apply GeneralPaperParameterCounterWords.ceiling
  omega

theorem root_CF (m k : ℕ) :
    GeneralPaperCFControlWords.width ((GeneralPaperProxyParameters.prepare m k).gridBits+3)≤word m k := by
  have ht := (terms m k).2.2.2.2.2.2
  have hw := measured m k _ ht
  change 64+binaryWordWidth ((GeneralPaperProxyParameters.prepare m k).gridBits+3+1)≤word m k
  have hEq : (GeneralPaperProxyParameters.prepare m k).gridBits+3+1=
      (GeneralPaperProxyParameters.prepare m k).gridBits+4 := by omega
  rw [hEq]
  exact hw

theorem source_CF (m k : ℕ) :
    GeneralPaperCFControlWords.width (GeneralPaperProxyParameters.alphabet m k).lambda≤word m k := by
  have hL := (alphabet_controls m k).1
  change (GeneralPaperProxyParameters.alphabet m k).lambda≤measure m k+2 at hL
  have hw := bounded m k ((GeneralPaperProxyParameters.alphabet m k).lambda+1) (by unfold cap; omega)
  exact hw

end Blotto.GeneralPaperPrecallLoopWords
