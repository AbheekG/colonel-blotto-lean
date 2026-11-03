import Blotto.GeneralPaperCalibratedClassifier
import Blotto.GeneralPaperSourceAlphabetLower

/-! Short paper-size envelope for the constructed shared control word.
The actual source alphabet dominates the root target, dimension and score
target. Thus the calibration is logarithmic in k and the source Lambda.
-/
namespace Blotto.GeneralPaperPrecallWordEnvelope
open GeneralPaperPrecallControlWord
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem source_target_word (m k : ℕ) :
    let a := GeneralPaperProxyParameters.alphabet m k
    binaryWordWidth (4*a.D*a.D)≤a.lambda := by
  let a := GeneralPaperProxyParameters.alphabet m k
  have hScale := GeneralPaperComparatorParameters.grid_scale_lower m k
    (GeneralPaperProxyParameters.prepare m k).qbar (GeneralPaperProxyParameters.cap_positive m k)
  change 4*a.D^2≤a.C at hScale
  have hPos := a.scalePositive
  have hLambda : 0<a.lambda := by
    by_contra hz
    have he : a.lambda=0 := by omega
    have hh := a.dyadic
    rw [he,pow_zero] at hh
    omega
  apply binaryWordWidth_le_of_lt_pow hLambda
  rw [←a.dyadic]
  nlinarith only [hScale,hPos]

theorem root_order (m k : ℕ) :
    (GeneralPaperProxyParameters.prepare m k).H≤(GeneralPaperProxyParameters.alphabet m k).D := by
  let r := GeneralPaperProxyParameters.prepare m k
  have hH := GeneralPaperProxyParameters.H_positive m k
  have hGrid := GeneralPaperProxyParameters.grid_lower m k
  have hSquare : r.H≤r.H*r.H := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left r.H (show 1≤r.H by exact hH)
  have hCap : r.H≤r.Qg := by change 4*r.H*r.H≤r.Qg at hGrid; nlinarith only [hGrid,hSquare]
  have hq : r.qbar=2*r.Qg := (GeneralPaperProxyParameters.data m k).2.2.2.2.2.2
  have hOrder := GeneralPaperSourceAlphabetLower.cap_le_order m k
  change r.qbar≤(GeneralPaperProxyParameters.alphabet m k).D at hOrder
  change r.H≤(GeneralPaperProxyParameters.alphabet m k).D
  omega

theorem root_target_word (m k : ℕ) :
    binaryWordWidth (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H)≤
      (GeneralPaperProxyParameters.alphabet m k).lambda := by
  have hH := root_order m k
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hH) hH
  exact (binaryWordWidth_mono hm).trans (source_target_word m k)

theorem labels (m k : ℕ) :
    (GeneralPaperComparatorParameters.countRun k).power=1024*(GeneralPaperScoreScaleParameters.prepare m k).K := by
  rw [GeneralPaperComparatorParameters.count_power,GeneralPaperScoreScaleParameters.label_power]
  have he : 17+k=(7+k)+10 := by omega
  rw [he,pow_add]
  norm_num
  omega

theorem score_target (m k : ℕ) :
    m*(GeneralPaperScoreScaleParameters.prepare m k).K≤
      (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J := by
  have hK := GeneralPaperScoreScaleParameters.labels_positive m k
  have hLabels := labels m k
  have hPred : (GeneralPaperScoreScaleParameters.prepare m k).K≤(GeneralPaperComparatorParameters.countRun k).power-1 := by omega
  have hm := Nat.mul_le_mul_left m hPred
  rw [(GeneralPaperComparatorParameters.data m k (GeneralPaperProxyParameters.prepare m k).qbar).2.1]
  omega

theorem alphabet_exponent (m k : ℕ) :
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).J≤
      (GeneralPaperProxyParameters.alphabet m k).lambda := by
  let r := GeneralPaperProxyParameters.prepare m k
  let a := GeneralPaperComparatorParameters.prepare m k r.qbar
  have hq := GeneralPaperProxyParameters.cap_positive m k
  have hData : a.D=r.qbar*(m+2)^a.J := (GeneralPaperComparatorParameters.data m k r.qbar).2.2.1
  have hPow : 2^a.J≤a.D := by
    rw [hData]
    have hb := Nat.pow_le_pow_left (by omega : 2≤m+2) a.J
    have hm := Nat.mul_le_mul_right ((m+2)^a.J) (show 1≤r.qbar by exact hq)
    exact hb.trans (by simpa only [one_mul] using hm)
  have he := GeneralPaperPrecallIndexWords.exponent_le_word a.J a.D hPow
  have hPos := GeneralPaperComparatorParameters.denominator_positive m k r.qbar hq
  have hSquare : a.D≤a.D*a.D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left a.D (show 1≤a.D by exact hPos)
  have hTarget : a.D≤4*a.D*a.D := by nlinarith only [hSquare]
  have hw := binaryWordWidth_mono hTarget
  have ht := source_target_word m k
  change binaryWordWidth (4*a.D*a.D)≤(GeneralPaperProxyParameters.alphabet m k).lambda at ht
  change a.J≤(GeneralPaperProxyParameters.alphabet m k).lambda
  omega

theorem root_exponent (m k : ℕ) :
    (GeneralPaperProxyParameters.prepare m k).d+2≤(GeneralPaperProxyParameters.alphabet m k).lambda := by
  let r := GeneralPaperProxyParameters.prepare m k
  have hPow : 2^(r.d+2)≤r.H := by
    rw [(GeneralPaperProxyParameters.data m k).2.2.2.1]
    exact Nat.pow_le_pow_left (by omega : 2≤m+3) _
  have he := GeneralPaperPrecallIndexWords.exponent_le_word (r.d+2) r.H hPow
  have hOrder := root_order m k
  have hw := binaryWordWidth_mono hOrder
  have hPos := (GeneralPaperProxyParameters.alphabet m k).orderPositive
  have hSquare : (GeneralPaperProxyParameters.alphabet m k).D≤
      (GeneralPaperProxyParameters.alphabet m k).D*(GeneralPaperProxyParameters.alphabet m k).D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (GeneralPaperProxyParameters.alphabet m k).D
      (show 1≤(GeneralPaperProxyParameters.alphabet m k).D by exact hPos)
  have hDT : (GeneralPaperProxyParameters.alphabet m k).D≤
      4*(GeneralPaperProxyParameters.alphabet m k).D*(GeneralPaperProxyParameters.alphabet m k).D := by nlinarith only [hSquare]
  have hDW := binaryWordWidth_mono hDT
  have ht := source_target_word m k
  change r.d+2≤(GeneralPaperProxyParameters.alphabet m k).lambda
  dsimp only [r] at *
  omega

theorem measure_bound (m k : ℕ) :
    measure m k≤k+8*(GeneralPaperProxyParameters.alphabet m k).lambda+64 := by
  let lambda := (GeneralPaperProxyParameters.alphabet m k).lambda
  have hRoot := root_target_word m k
  have hSource := source_target_word m k
  change binaryWordWidth (4*(GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).D*
    (GeneralPaperComparatorParameters.prepare m k (GeneralPaperProxyParameters.prepare m k).qbar).D)≤lambda at hSource
  have hA := alphabet_exponent m k
  have hR := root_exponent m k
  have hS := score_target m k
  have hAWord := (binaryWordWidth_mono hA).trans (GeneralPaperInitializerControlCounters.word_le_self lambda)
  have hRWord := (binaryWordWidth_mono hR).trans (GeneralPaperInitializerControlCounters.word_le_self lambda)
  have hSWord := (binaryWordWidth_mono (hS.trans hA)).trans (GeneralPaperInitializerControlCounters.word_le_self lambda)
  have hg0 := GeneralPaperPowerCeiling.loop_depth
    (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H) 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling
    (4*(GeneralPaperProxyParameters.prepare m k).H*(GeneralPaperProxyParameters.prepare m k).H)).doublings≤_ at hg0
  rw [←(GeneralPaperProxyParameters.data m k).2.2.2.2.2.1] at hg0
  unfold GeneralPaperPrecallControlWord.measure
  dsimp only
  dsimp only [lambda] at *
  omega

theorem word_bound (m k : ℕ) :
    word m k≤192+8*binaryWordWidth (k+1)+8*binaryWordWidth ((GeneralPaperProxyParameters.alphabet m k).lambda+1) := by
  let lambda := (GeneralPaperProxyParameters.alphabet m k).lambda
  have hm := measure_bound m k
  have hProduct : measure m k+1≤128*(k+1)*(lambda+1) := by
    change measure m k≤k+8*lambda+64 at hm
    nlinarith only [hm,Nat.zero_le (k*lambda)]
  have hw := binaryWordWidth_mono hProduct
  have h1 := binaryWordWidth_mul (128*(k+1)) (lambda+1)
  have h2 := binaryWordWidth_mul 128 (k+1)
  have h128 : binaryWordWidth 128=8 := by decide
  unfold word
  change _≤192+8*binaryWordWidth (k+1)+8*binaryWordWidth (lambda+1)
  omega

end Blotto.GeneralPaperPrecallWordEnvelope
