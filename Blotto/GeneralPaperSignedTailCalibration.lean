import Blotto.GeneralPaperCatalogueOptionPlans

/-! The actual dyadic alphabet derives the signed-tail code words. No
floating-point word bound is substituted for the full code/endpoint width.
These are analytical inequalities, not encoding or calibration passes.
-/
namespace Blotto.GeneralPaperSignedTailCalibration
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem cut_width (m height : ℕ) :
    GeneralPaperSignedCutOperands.width m (2^height)≤320+16*binaryWordWidth (m+2)+32*height := by
  have h := GeneralPaperSourceRankCache.code_word height
  unfold GeneralPaperSignedCutOperands.width
  omega

theorem tail_width (m k height : ℕ) :
    GeneralPaperSignedTailOperands.width m k (2^height)≤
      1024+32*(35+k)+64*height+48*binaryWordWidth (m+2) := by
  have hShift : 2*2^height=2^(height+1) := by rw [pow_succ]; omega
  have h := GeneralPaperSourceRankCache.rank_width (m+1) (35+k) (height+1)
  change _≤512+32*(35+k)+64*(height+1)+16*binaryWordWidth (m+2) at h
  unfold GeneralPaperSignedTailOperands.width
  rw [hShift]
  omega

theorem actual_words (m k : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    GeneralPaperSignedCutOperands.width m (8*a.C)≤320+16*binaryWordWidth (m+2)+32*a.lambda ∧
    GeneralPaperSignedTailOperands.width m k (8*a.C)≤
      1024+32*(35+k)+64*a.lambda+48*binaryWordWidth (m+2) := by
  rw [a.dyadic]
  exact ⟨cut_width m a.lambda,tail_width m k a.lambda⟩

end Blotto.GeneralPaperSignedTailCalibration
