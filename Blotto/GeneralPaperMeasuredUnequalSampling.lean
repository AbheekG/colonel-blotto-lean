import Blotto.GeneralPaperEnlargedReferenceHeadlines

/-! Sampling and compact descriptions of the actual one-pass measured
unequal producer. The mathematical native problem view is erased. -/
namespace Blotto.GeneralPaperMeasuredUnequalSampling
open GeneralPaperNativeResourceDomain
open GeneralPaperNativeWorkingSpaceHeadline (epsilon)
open GeneralPaperEnlargedReferenceSourceTime (Reference)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def actual (model : RationalCostModel) (K : ℕ) (p : Problem) : GeneralPaperClosedStrategyDriver.Prepared p.n :=
  (GeneralPaperMeasuredUnequalPreparation.run model 1 K
    (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2).1

theorem data (model : RationalCostModel) (K : ℕ) (p : Problem) :
    actual model K p = GeneralPaperArbitraryPreparationDraw.returned model
      (GeneralPaperMeasuredReferenceGrowth.word model K p) p :=
  GeneralPaperMeasuredUnequalPreparation.data model 1 K (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2

theorem draw_contract {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (K : ℕ) (p : Problem) (hOne : epsilon p < 1) :
    GeneralPaperArbitraryPreparationDraw.Contract model C d p (actual model K p) := by
  rw [data]
  exact GeneralPaperArbitraryPreparationDraw.at_word hg _ p hOne

theorem description_headline {model : RationalCostModel} {C d : ℕ} (K : ℕ) (cal : Reference model C d)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    ∃ A : ℕ, ∀ p : Problem, epsilon p < 1 →
      let returned := actual model K p
      let o := returned.raw.strategies.original.reduced
      let k := returned.raw.exponent
      let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
      ∃ sampler : GeneralPaperStoredStrategySampler.Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
        returned.sampler = some sampler ∧
        (GeneralPaperClosedDescriptionStorage.footprint (cal.word p) sampler : ℚ) ≤
          (A : ℚ) * GeneralPaperNativeReturnedDescriptionHeadline.descriptionScale p *
            (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ 2 ∧
        (GeneralPaperClosedDescriptionStorage.preparedFoot (cal.word p) returned : ℚ) ≤
          (A : ℚ) * GeneralPaperNativeReturnedDescriptionHeadline.descriptionScale p *
            (GeneralPaperNativeWorkingSpaceHeadline.paperLog p : ℚ) ^ 2 := by
  obtain ⟨A, hA⟩ := GeneralPaperEnlargedReferenceDescription.native_bit_return_description cal
  refine ⟨A, fun p hOne => ?_⟩
  dsimp only
  rw [data, ← congrFun hWord p]
  exact hA p hOne

end Blotto.GeneralPaperMeasuredUnequalSampling
