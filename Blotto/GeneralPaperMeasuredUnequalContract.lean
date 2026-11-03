import Blotto.GeneralPaperMeasuredEqualContract

/-! The actual measured unequal return satisfies the shared canonical-law
and every-fresh-string contracts at its local sampling reference. -/
namespace Blotto.GeneralPaperMeasuredUnequalContract
open GeneralPaperOriginalGameInput GeneralPaperAllBranchBitDispatch GeneralPaperAllBranchBitLaw
open GeneralPaperAllBranchBitOutput
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem actual_contract (model : RationalCostModel) (A K : ℕ) (p : Input) (hStrict : p.budget < 1)
    (hOne : epsilon p < 1) :
    Guarantee model K p (.unequal (GeneralPaperMeasuredUnequalPreparation.run model A K p hStrict).1) ∧
      Pointwise model K p (.unequal (GeneralPaperMeasuredUnequalPreparation.run model A K p hStrict).1) := by
  rw [GeneralPaperMeasuredUnequalPreparation.data]
  let W := K * GeneralPaperOriginalReferenceComparison.logarithm model p
  let actual := (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1, hStrict⟩).1
  change Guarantee model K p (.unequal actual) ∧ Pointwise model K p (.unequal actual)
  obtain ⟨sampler, hSampler, _⟩ := GeneralPaperClosedStrategyEquilibrium.bit_epsilon model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget ⟨p.budget_valid.1, hStrict⟩ model.rat
  have hG := GeneralPaperNativeSamplerViewAndLaw.native_epsilon_at_draw_reference true model.rat
    (GeneralPaperClosedBitSampling.reference p.n actual.raw.strategies.original.reduced.m actual.raw.exponent)
    model W W W p.words (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1, hStrict⟩ sampler hSampler
  change actual.sampler = some sampler at hSampler
  constructor
  · dsimp only [Guarantee, law]
    simp only [hSampler, Option.elim_some]
    exact ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩
  · dsimp only [Pointwise]
    simp only [hSampler, Option.elim_some]
    exact hG.2.2.2.2

end Blotto.GeneralPaperMeasuredUnequalContract
