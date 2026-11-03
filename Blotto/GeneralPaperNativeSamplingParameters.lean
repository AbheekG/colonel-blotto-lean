import Blotto.GeneralPaperSamplingOperandEnvelope

/-! Explicit native source/sample parameters. The short-control envelope
is logarithmic in original n and inverse accuracy. Both source dictionary
anchor heights retain one field and one inverse-accuracy factor. -/
namespace Blotto.GeneralPaperNativeSamplingParameters
open GeneralPaperSamplingOperandEnvelope
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def logarithm (n k B : ℕ) : ℕ := 128+k+binaryWordWidth (n+4)+binaryWordWidth (B+1)
def scale (m k : ℕ) : ℕ := (m+1)*2^k

theorem log_positive (n k B : ℕ) : 1≤logarithm n k B := by unfold logarithm;omega

theorem representative_word (k : ℕ) : binaryWordWidth (GeneralPaperLightFieldReduction.representatives k)≤k+5 := by
  unfold GeneralPaperLightFieldReduction.representatives
  have h := binaryWordWidth_mul 8 (2^k)
  rw [show binaryWordWidth 8=4 by decide,
    show binaryWordWidth (2^k)=k+1 by simp only [binaryWordWidth,Nat.log2_two_pow]] at h
  omega

theorem control_size (n m k B W : ℕ) (hm : m≤n) (hW : binaryWordWidth W≤binaryWordWidth n+k+10) :
    controlSize (GeneralPaperClosedBitSampling.reference n m k)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rowBits
      (k+6) (GeneralPaperLightFieldReduction.representatives k) W (GeneralPaperNativeSelectedSecurity.count k)≤
      16*logarithm n k B := by
  let R := GeneralPaperLightFieldReduction.representatives k
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k
  have hR := representative_word k
  have hS : binaryWordWidth (GeneralPaperNativeSelectedSecurity.count k)=k+7 := by
    rw [GeneralPaperNativeSelectedSecurity.count_power]
    simp only [binaryWordWidth,Nat.log2_two_pow]
  have hBits := GeneralPaperCachedArithmeticSampling.row_bits m n k hm
  have hT := word_add t.rows 1
  rw [GeneralPaperTrajectoryParameters.rows_power] at hT
  rw [show binaryWordWidth (2^t.rowBits)=t.rowBits+1 by simp only [binaryWordWidth,Nat.log2_two_pow],
    show binaryWordWidth 1=1 by decide] at hT
  rw [←GeneralPaperTrajectoryParameters.rows_power] at hT
  have h2 := word_add (2*n+R) 2
  have h3 := word_add (2*n) R
  have h4 := binaryWordWidth_mul 2 n
  rw [show binaryWordWidth 2=2 by decide] at h2 h4
  have hn := binaryWordWidth_mono (show n≤n+4 by omega)
  dsimp only [R,t] at h2 h3 hT
  unfold controlSize GeneralPaperClosedBitSampling.reference logarithm
  omega

theorem anchor_height (m k : ℕ) :
    GeneralPaperSourcePairAnchorHeights.width m k≤16777216*scale m k*binaryWordWidth (m+3) := by
  let w := binaryWordWidth (m+3)
  let p := 2^k
  have hK : (GeneralPaperProxyParameters.prepare m k).K=128*p := by
    rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.label_power]
    dsimp only [p]
    norm_num [pow_add]
  have hD : (GeneralPaperProxyParameters.prepare m k).d≤128*m*p := by
    change m*((GeneralPaperProxyParameters.prepare m k).K-1)≤_
    rw [hK]
    have h := Nat.mul_le_mul_left m (Nat.sub_le (128*p) 1)
    nlinarith only [h]
  have hC : (GeneralPaperComparatorParameters.countRun k).power=131072*p := by
    rw [GeneralPaperComparatorParameters.count_power]
    dsimp only [p]
    norm_num [pow_add]
  have hCW : (m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)*binaryWordWidth (m+2)≤
      (131072*m*p+1)*w := by
    apply Nat.mul_le_mul
    · rw [hC]
      have h := Nat.mul_le_mul_left m (Nat.sub_le (131072*p) 1)
      nlinarith only [h]
    · exact binaryWordWidth_mono (by omega)
  have hDW := Nat.mul_le_mul_right w (Nat.add_le_add_right hD 2)
  have hLambda := GeneralPaperProxyWidths.lambda_bound m k
  have hLambda' : (GeneralPaperProxyParameters.alphabet m k).lambda≤24+4*(128*m*p+2)*w+2*(131072*m*p+1)*w := by
    nlinarith only [hLambda,hCW,hDW]
  have hSource := GeneralPaperSourceAlphabetLower.anchor_height m k
  have hEndpoint := GeneralPaperEndpointDictionarySize.dimension_bound m k
  have hw : 1≤w := binaryWordWidth_pos _
  have hp : 1≤p := Nat.one_le_two_pow
  have hwp : w≤p*w := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right w hp
  unfold GeneralPaperSourcePairAnchorHeights.width scale
  dsimp only [w,p] at hSource hLambda' hEndpoint hDW hwp hw ⊢
  apply max_le
  · nlinarith only [hSource,hLambda',hwp,hw,Nat.zero_le (m*2^k*binaryWordWidth (m+3))]
  · nlinarith only [hEndpoint,hDW,hwp,hw,Nat.zero_le (m*2^k*binaryWordWidth (m+3))]

end Blotto.GeneralPaperNativeSamplingParameters
