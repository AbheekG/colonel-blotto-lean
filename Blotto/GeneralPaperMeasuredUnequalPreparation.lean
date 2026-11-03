import Blotto.GeneralPaperClosedParsedPreparation
import Blotto.GeneralPaperMeasuredReferenceGrowth

/-! The unequal original-input producer executes one accuracy preparation,
one reference measurement and one continuation at that measured word.
Proof-side resource reserves are absent from the executed definition. -/
namespace Blotto.GeneralPaperMeasuredUnequalPreparation
open GeneralPaperOriginalGameInput
open GeneralPaperOriginalReferenceComparison (logarithm)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def run (model : RationalCostModel) (A K : ℕ) (p : Input) (h : p.budget < 1) :
    GeneralPaperClosedStrategyDriver.Prepared p.n × ℕ :=
  let initial := GeneralPaperOriginalMeasuredReference.prepare model A K p
  let actual := GeneralPaperClosedParsedPreparation.run model initial.1.2 initial.1.2 initial.1.2
    initial.1.1 p.values p.selector p.correct p.budget ⟨p.budget_valid.1, h⟩
  (actual.1, initial.2 + actual.2 + 64 * (A + initial.1.2 + 1))

theorem data (model : RationalCostModel) (A K : ℕ) (p : Input) (h : p.budget < 1) :
    (run model A K p h).1 =
      (GeneralPaperClosedStrategyDriver.bit model (K * logarithm model p) (K * logarithm model p)
        (K * logarithm model p) p.words p.values p.selector p.correct p.budget ⟨p.budget_valid.1, h⟩).1 := by
  dsimp only [run]
  rw [GeneralPaperClosedParsedPreparation.data, GeneralPaperOriginalMeasuredReference.words,
    GeneralPaperOriginalMeasuredReference.word]

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input) (h : p.budget < 1) :
    (run model A K p h).2 ≤
      GeneralPaperEqualInputInitialization.initializationPrice model A K (equalInput model p) +
      (GeneralPaperClosedStrategyDriver.bit model (K * logarithm model p) (K * logarithm model p)
        (K * logarithm model p) p.words p.values p.selector p.correct p.budget ⟨p.budget_valid.1, h⟩).2 +
      64 * (A + K * logarithm model p + 1) := by
  let initial := GeneralPaperOriginalMeasuredReference.prepare model A K p
  have hi := GeneralPaperOriginalMeasuredReference.work model A K p
  have hc := GeneralPaperClosedParsedPreparation.work_le model initial.1.2 initial.1.2 initial.1.2
    initial.1.1 p.values p.selector p.correct p.budget ⟨p.budget_valid.1, h⟩
  have hs := Nat.add_le_add_right (Nat.add_le_add hi hc) (64 * (A + initial.1.2 + 1))
  simpa only [run, initial, GeneralPaperOriginalMeasuredReference.words,
    GeneralPaperOriginalMeasuredReference.word] using hs

theorem equilibrium (model : RationalCostModel) (A K : ℕ) (p : Input) (h : p.budget < 1)
    (hOne : epsilon p < 1) :
    let prepared := (run model A K p h).1
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler p.n
      (GeneralPaperTrajectoryParameters.prepare
        (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda
        prepared.raw.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K,
      prepared.sampler = some sampler ∧ GeneralPaperClosedStrategyEquilibrium.Guarantee true model.rat
        (K * logarithm model p) model p.selector.values (p.budget : ℝ) (epsilon p : ℝ) sampler := by
  dsimp only
  rw [data]
  exact GeneralPaperClosedStrategyEquilibrium.bit_epsilon model _ _ _ p.words (epsilon p)
    (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget ⟨p.budget_valid.1, h⟩ model.rat

end Blotto.GeneralPaperMeasuredUnequalPreparation
