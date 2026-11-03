import Blotto.GeneralPaperMeasuredInitializerMonotonicity

/-! Exact one-pass initializer repricing transfers the complete established
equal preparation work bound to the retained-word executable producer. -/
namespace Blotto.GeneralPaperMeasuredEqualWork
open GeneralPaperOriginalGameInput
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem copied_mono (model : RationalCostModel) (A B K : ℕ) (h : A ≤ B)
    (p : GeneralPaperEqualInputDomain.Input model) :
    (GeneralPaperEqualCopiedPipeline.run model A K p).2 ≤ (GeneralPaperEqualCopiedPipeline.run model B K p).2 := by
  rw [GeneralPaperEqualCopiedPipeline.work, GeneralPaperEqualCopiedPipeline.work]
  exact Nat.add_le_add_right (GeneralPaperMeasuredInitializerMonotonicity.initialization model A B K h p) _

theorem pipeline_mono (model : RationalCostModel) (A B K : ℕ) (h : A ≤ B)
    (p : GeneralPaperEqualInputDomain.Input model) :
    (GeneralPaperStoredSelectedPipeline.run model A K p).2 ≤
      (GeneralPaperStoredSelectedPipeline.run model B K p).2 := by
  rw [GeneralPaperCompleteStoredPipelineWork.work_identity, GeneralPaperCompleteStoredPipelineWork.work_identity]
  have hs : (GeneralPaperEqualCopiedPipeline.run model A K p).1 =
      (GeneralPaperEqualCopiedPipeline.run model B K p).1 := by
    rw [GeneralPaperEqualCopiedPipeline.data, GeneralPaperEqualCopiedPipeline.data]
  rw [hs]
  exact Nat.add_le_add_right (Nat.add_le_add_right (copied_mono model A B K h p) _) _

theorem work (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Input) :
    (GeneralPaperMeasuredEqualPreparation.run model 1 K p).2 ≤
      GeneralPaperCompleteStoredPipelineWork.price model K (equalInput model p) := by
  have hW : 1 ≤ GeneralPaperEqualInputDomain.word K (equalInput model p) :=
    Nat.mul_le_mul hK (GeneralPaperEqualInputDomain.logarithm_positive (equalInput model p))
  rw [GeneralPaperMeasuredEqualPreparation.work]
  exact (pipeline_mono model 1 _ K hW (equalInput model p)).trans
    (GeneralPaperCompleteStoredPipelineWork.work model K (equalInput model p))

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ A e : ℕ, ∀ p : Input,
      (GeneralPaperMeasuredEqualPreparation.run model 1 K p).2 ≤
        A * GeneralPaperEqualInputHeadline.inputSize (equalInput model p) *
          (GeneralPaperEqualInputHeadline.paperLog (equalInput model p)) ^ e := by
  obtain ⟨A, e, h⟩ := GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperCompleteStoredPipelineWork.price_rate model hFast K)
  exact ⟨A, e, fun p => (work model K hK p).trans (h (equalInput model p))⟩

end Blotto.GeneralPaperMeasuredEqualWork
