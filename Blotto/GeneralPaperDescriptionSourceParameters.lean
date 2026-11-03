import Blotto.GeneralPaperDescriptionSizeAlgebra

/-! The literal full trajectory, anchor dictionaries and sorted-reference
tables have retained-description degree (2,0,3). Reference W stays explicit
for the later whole-program common-word join; original B remains additive. -/
namespace Blotto.GeneralPaperDescriptionSourceParameters
open GeneralPaperDescriptionSizeAlgebra
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 16384

theorem labels (m k : ℕ) : (GeneralPaperProxyParameters.prepare m k).K=128*2^k := by
  rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.label_power]
  norm_num [pow_add]

theorem alphabet (m k : ℕ) :
    (GeneralPaperProxyParameters.alphabet m k).lambda+2≤2097152*(m+1)*2^k*binaryWordWidth (m+3) := by
  let w := binaryWordWidth (m+3)
  let p := 2^k
  have hD : (GeneralPaperProxyParameters.prepare m k).d≤128*m*p := by
    change m*((GeneralPaperProxyParameters.prepare m k).K-1)≤_
    rw [labels]
    have h := Nat.mul_le_mul_left m (Nat.sub_le (128*p) 1)
    nlinarith only [h]
  have hC : (GeneralPaperComparatorParameters.countRun k).power=131072*p := by
    rw [GeneralPaperComparatorParameters.count_power]
    dsimp only [p]
    norm_num [pow_add]
  have hCW : (m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)*binaryWordWidth (m+2)≤(131072*m*p+1)*w := by
    apply Nat.mul_le_mul
    · rw [hC]
      have h := Nat.mul_le_mul_left m (Nat.sub_le (131072*p) 1)
      nlinarith only [h]
    · exact binaryWordWidth_mono (by omega)
  have hDW := Nat.mul_le_mul_right w (Nat.add_le_add_right hD 2)
  have hLambda := GeneralPaperProxyWidths.lambda_bound m k
  have hw : 1≤w := binaryWordWidth_pos _
  have hp : 1≤p := Nat.one_le_two_pow
  have hwp : w≤p*w := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right w hp
  dsimp only [w,p] at hCW hDW hw hwp
  nlinarith only [hLambda,hCW,hDW,hw,hwp,Nat.zero_le (m*2^k*binaryWordWidth (m+3))]

theorem rows (m k : ℕ) :
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows≤
      2^68*(m+1)*(2^k)^3*binaryWordWidth (m+3) := by
  let lambda := (GeneralPaperProxyParameters.alphabet m k).lambda
  have hT : (GeneralPaperTrajectoryParameters.prepare lambda k).rows≤2*(lambda+2)*2^(35+k)*2^(11+k) := by
    rw [GeneralPaperTrajectoryParameters.rows_product,GeneralPaperTrajectoryParameters.period_power]
    exact (Nat.mul_le_mul_right _ (GeneralPaperTrajectoryParameters.epochs_upper lambda k).le).trans_eq (by ring)
  have hL := alphabet m k
  calc
    _≤2*(lambda+2)*2^(35+k)*2^(11+k) := hT
    _≤2*(2097152*(m+1)*2^k*binaryWordWidth (m+3))*2^(35+k)*2^(11+k) := by gcongr
    _=2^68*(m+1)*(2^k)^3*binaryWordWidth (m+3) := by simp only [pow_add];norm_num;ring

theorem control_words (W n m k : ℕ) (hm : m≤n) :
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k
    binaryWordWidth (GeneralPaperProxyParameters.prepare m k).K≤word W n k ∧
      binaryWordWidth t.rows≤4*word W n k ∧ binaryWordWidth t.rowBits≤4*word W n k := by
  have hBits := GeneralPaperCachedArithmeticSampling.row_bits m n k hm
  have hRb := GeneralPaperSamplingFastBitBound.word_self
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rowBits
  have hK : binaryWordWidth (GeneralPaperProxyParameters.prepare m k).K=k+8 := by
    rw [(GeneralPaperProxyParameters.data m k).1,GeneralPaperScoreScaleParameters.label_power]
    simp only [binaryWordWidth,Nat.log2_two_pow]
    omega
  have hT : binaryWordWidth (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows=
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rowBits+1 := by
    rw [GeneralPaperTrajectoryParameters.rows_power]
    simp only [binaryWordWidth,Nat.log2_two_pow]
  dsimp only
  unfold word
  omega

def structural (n m k : ℕ) : ℕ := n+1+(m+1)^2*(2^k)^3

theorem shape_bound (W n m k : ℕ) (hm : m≤n) :
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k
    let K := (GeneralPaperProxyParameters.prepare m k).K
    let H := GeneralPaperSourcePairAnchorHeights.width m k
    shape n m t.rows K H*word W n k≤2^70*structural n m k*(word W n k)^2 := by
  let p := 2^k
  let w := binaryWordWidth (m+3)
  let P := word W n k
  let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
  let K := (GeneralPaperProxyParameters.prepare m k).K
  let H := GeneralPaperSourcePairAnchorHeights.width m k
  have hT := rows m k
  have hH := GeneralPaperNativeSamplingParameters.anchor_height m k
  change H≤16777216*((m+1)*p)*w at hH
  have hp : 1≤p := Nat.one_le_two_pow
  have hw : 1≤w := binaryWordWidth_pos _
  have hBase : 1≤(m+1)*p*w := Nat.mul_pos (Nat.mul_pos (by omega) (Nat.two_pow_pos k)) (binaryWordWidth_pos _)
  have hH' : H+1≤16777217*(m+1)*p*w := by nlinarith only [hH,hBase]
  have hMT : m*T≤2^68*(m+1)^2*p^3*w := by
    have h := Nat.mul_le_mul (show m≤m+1 by omega) hT
    exact h.trans_eq (by dsimp only [p,w];ring)
  have hMK : m*K≤128*(m+1)*p := by
    dsimp only [K]
    rw [labels]
    have h := Nat.mul_le_mul_right (128*p) (show m≤m+1 by omega)
    dsimp only [p] at h ⊢
    nlinarith only [h]
  have hp3 : p^2≤p^3 := Nat.pow_le_pow_right hp (by omega)
  have hMKH : m*K*(H+1)≤4294967296*(m+1)^2*p^3*w := by
    calc
      _≤(128*(m+1)*p)*(16777217*(m+1)*p*w) := Nat.mul_le_mul hMK hH'
      _=2147483776*(m+1)^2*p^2*w := by ring
      _≤4294967296*(m+1)^2*p^3*w := by gcongr;decide
  have hP : 1≤P := word_positive W n k
  have hwP : w≤P := by
    have h := binaryWordWidth_mono (show m+3≤n+4 by omega)
    dsimp only [w,P,word]
    omega
  have hShape : shape n m T K H≤n+1+(2^68+4294967296)*(m+1)^2*p^3*P := by
    have hBound := Nat.mul_le_mul_left ((2^68+4294967296)*(m+1)^2*p^3) hwP
    unfold shape
    nlinarith only [hMT,hMKH,hBound]
  have hTotal := Nat.mul_le_mul_right P hShape
  have hNP := Nat.mul_le_mul_left (n+1) (show P≤P^2 by nlinarith only [hP])
  change shape n m T K H*P≤2^70*structural n m k*P^2
  unfold structural
  dsimp only [p] at hTotal hNP ⊢
  norm_num only [Nat.reducePow] at hTotal ⊢
  nlinarith only [hTotal,hNP,Nat.zero_le ((m+1)^2*(2^k)^3*P^2),Nat.zero_le ((n+1)*P^2)]

end Blotto.GeneralPaperDescriptionSourceParameters
