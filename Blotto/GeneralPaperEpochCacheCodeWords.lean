import Blotto.GeneralPaperEncodedCellPlans

/-! Actual summary and catalogue code bounds supply the full code word.
Neither floating/mesh words nor a supplied coordinate-height oracle replace
this bound. These are erased consequences of retained native metadata. -/
namespace Blotto.GeneralPaperEpochCacheCodeWords
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueEpochMetadata
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem summary_word {m k : ℕ} (cache : Cache m k) (hc : CodesValid cache) (learner : Learner) (j : Fin m)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    1+binaryWordWidth ((summary learner cache j).read r)≤GeneralPaperDecoderControls.operandWidth cache.alphabet.lambda := by
  have hw := hc learner j r
  rw [width_power] at hw
  apply GeneralPaperEncodedSignedPlans.code_word
  exact hw.le.trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (height_bound learner cache))

theorem option_word {m k : ℕ} (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    1+binaryWordWidth ((ready.data.codes.read j).read i)≤GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda := by
  have h := GeneralPaperCatalogueArrays.code_bound ready.alphabet ready.response k ready.summaries j i
  rw [←ready.data_spec,ready.alphabet.dyadic] at h
  apply GeneralPaperEncodedSignedPlans.code_word
  exact h.le.trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega))

theorem unsigned_width (a : GeneralPaperCodeAlphabet.Alphabet) :
    1+binaryWordWidth (8*a.C)≤GeneralPaperDecoderControls.operandWidth a.lambda := by
  apply GeneralPaperEncodedSignedPlans.code_word
  rw [a.dyadic]
  exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega)

theorem alphabet_scalars (a : GeneralPaperCodeAlphabet.Alphabet) :
    1+binaryWordWidth a.D≤GeneralPaperDecoderControls.operandWidth a.lambda ∧
    1+binaryWordWidth a.C≤GeneralPaperDecoderControls.operandWidth a.lambda ∧
    1+binaryWordWidth a.lambda≤GeneralPaperDecoderControls.operandWidth a.lambda := by
  have hD : a.D≤a.C := by
    have h := Nat.mul_le_mul_left a.D (show 1≤a.D by have h:=a.orderPositive; omega)
    simp only [Nat.mul_one] at h
    exact h.trans a.separated
  have hC : a.C≤2^(a.lambda+1) := by
    have h : a.C≤8*a.C := by omega
    rw [a.dyadic] at h
    exact h.trans (Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega))
  have hw := GeneralPaperInitializerControlCounters.word_le_self a.lambda
  refine ⟨GeneralPaperEncodedSignedPlans.code_word a.lambda a.D (hD.trans hC),
    GeneralPaperEncodedSignedPlans.code_word a.lambda a.C hC,?_⟩
  unfold GeneralPaperDecoderControls.operandWidth
  omega

end Blotto.GeneralPaperEpochCacheCodeWords
