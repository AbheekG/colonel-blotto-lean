import Blotto.GeneralPaperScoreBasisControls

/-! The actual selected alphabet has Lambda at least the field count.
Its closed-candidate and normalized-anchor heights are O(Lambda), using
constructed denominator caps rather than an input width assumption.
-/
namespace Blotto.GeneralPaperSourceAlphabetLower
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem order_le_scale (a : GeneralPaperCodeAlphabet.Alphabet) : a.D≤a.C := by
  have hp := a.orderPositive
  have hs := a.separated
  nlinarith only [hp,hs]

theorem cap_le_order (m k : ℕ) : (prepare m k).qbar≤(alphabet m k).D := by
  have hp : 0<(m+2)^(m*((GeneralPaperComparatorParameters.countRun k).power-1)+1) := by positivity
  change (prepare m k).qbar≤(GeneralPaperComparatorParameters.prepare m k (prepare m k).qbar).D
  rw [(GeneralPaperComparatorParameters.data m k (prepare m k).qbar).2.2.1]
  nlinarith only [hp]

theorem exponential_order (m k : ℕ) : 2^m≤(alphabet m k).D := by
  have hK : 2≤(GeneralPaperComparatorParameters.countRun k).power := by
    rw [GeneralPaperComparatorParameters.count_power]
    exact Nat.one_lt_pow (by omega : 17+k≠0) (by decide : 1<(2:ℕ))
  have hJ : m≤m*((GeneralPaperComparatorParameters.countRun k).power-1)+1 := by
    nlinarith only [Nat.mul_le_mul_left m (show 1≤(GeneralPaperComparatorParameters.countRun k).power-1 by omega)]
  have hBase : (2:ℕ)^m≤(m+2)^m := Nat.pow_le_pow_left (by omega) m
  have hPower := Nat.pow_le_pow_right (by omega : 0<m+2) hJ
  have hq := cap_positive m k
  change _≤(GeneralPaperComparatorParameters.prepare m k (prepare m k).qbar).D
  rw [(GeneralPaperComparatorParameters.data m k (prepare m k).qbar).2.2.1]
  exact (hBase.trans hPower).trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right
      ((m+2)^(m*((GeneralPaperComparatorParameters.countRun k).power-1)+1)) (show 1≤(prepare m k).qbar by omega))

theorem fields_le_lambda (m k : ℕ) : m≤(alphabet m k).lambda := by
  have hd := exponential_order m k
  have hs := order_le_scale (alphabet m k)
  have hp : (alphabet m k).C≤8*(alphabet m k).C := by omega
  have he := hd.trans (hs.trans hp)
  rw [(alphabet m k).dyadic] at he
  exact (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp he

theorem scale_width (a : GeneralPaperCodeAlphabet.Alphabet) : binaryWordWidth a.C≤a.lambda+1 := by
  apply binaryWordWidth_le_of_lt_pow (by omega : 0<a.lambda+1)
  rw [pow_succ,←a.dyadic]
  have hp := a.scalePositive
  omega

theorem anchor_height (m k : ℕ) : GeneralPaperSourceScoreHeights.anchorHeight m k≤2*((alphabet m k).lambda+1) := by
  have hc := scale_width (alphabet m k)
  have hq := binaryWordWidth_mono ((cap_le_order m k).trans (order_le_scale (alphabet m k)))
  unfold GeneralPaperSourceScoreHeights.anchorHeight
  omega

theorem score_width (m k Qv : ℕ) :
    GeneralPaperScoreMatrixEnvelope.width (binaryWordWidth Qv) (GeneralPaperSourceScoreHeights.anchorHeight m k)
      (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).K≤
        1+2*(binaryWordWidth Qv+3*binaryWordWidth (prepare m k).S+2*binaryWordWidth (prepare m k).K+2*(alphabet m k).lambda+13) := by
  have hd := GeneralPaperScoreBasisControls.depth m k
  have ha := anchor_height m k
  unfold GeneralPaperScoreMatrixEnvelope.width
  omega

end Blotto.GeneralPaperSourceAlphabetLower
