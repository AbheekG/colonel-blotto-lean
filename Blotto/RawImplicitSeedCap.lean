import Blotto.RawImplicitSecurityState
import Blotto.GenericImplicitSeedCap
import Blotto.ImplicitTrainingTransition
import Blotto.AdaptiveSamplingPrecision

/-! Raw compact trainer draws have a horizon-local computed polynomial seed
cap. Actual block growth, aggregate decay and guide sizes supply its premises;
no next-step width oracle is accepted. Decoder properties and input code-width
certificates remain explicit. Seed storage is not complete runtime pricing. -/

namespace Blotto
open scoped Classical
namespace ProductSecurityTrainer
open ImplicitLeafCounts

def compactLeafSeedCap (n T A : ℕ) (epsilon : ℚ) : ℕ :=
  ProposalTree.polynomialSeedCap (n + 1) (2 * n + 1) T A ((n + 1) * A + 2 * T)
    (6 + binaryWordWidth (32 * epsilon).den)

theorem compactPreparedA_seedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (T A : ℕ) (hT : history.length ≤ T)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ A) (epsilon : ℚ) (he : 0 < epsilon) :
    (c.compactPreparedA cfg history).bitBudget epsilon ≤ compactLeafSeedCap n T A epsilon := by
  have hn : ∀ field code, code ≤ cfg.capsA field → 0 ≤ bidDecoder c.bidsA field code := by
    intro field code hc
    have hs := congrFun cfg.sizesA field
    have hi : code < c.sizesA field := by omega
    simp only [bidDecoder, hi, dite_true]
    exact c.bidsA_nonnegative _ _
  exact genericTree_epsilon_horizon_seed_bound n cfg.capsA (bidDecoder c.bidsA) cfg.orderedA hn cfg.zeroA
    rawSelected (fun _ x => x.2.1 x.2.2) c.eta c.theta c.eta_unit c.theta_unit history T A hT hA epsilon he

theorem compactPreparedB_seedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (T A : ℕ) (hT : history.length ≤ T)
    (hA : ∀ field, binaryWordWidth (cfg.capsB field + 1) ≤ A) (epsilon : ℚ) (he : 0 < epsilon) :
    (c.compactPreparedB cfg history).bitBudget epsilon ≤ compactLeafSeedCap n T A epsilon := by
  have hn : ∀ field code, code ≤ cfg.capsB field → 0 ≤ bidDecoder c.bidsB field code := by
    intro field code hc
    have hs := congrFun cfg.sizesB field
    have hi : code < c.sizesB field := by omega
    simp only [bidDecoder, hi, dite_true]
    exact c.bidsB_nonnegative _ _
  exact genericTree_epsilon_horizon_seed_bound n cfg.capsB (bidDecoder c.bidsB) cfg.orderedB hn cfg.zeroB
    rawSelected (fun _ x => x.1 x.2.2) c.eta c.theta c.eta_unit c.theta_unit history T A hT hA epsilon he

def compactTransitionSeedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (T AA AB : ℕ)
    (epsilonA epsilonB : ℚ) (K : ℕ) : ℕ :=
  compactLeafSeedCap n T AA epsilonA + compactLeafSeedCap n T AB epsilonB + c.values.attempt.bitBudget K

theorem compactTransition_seedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (history : List (RawObservation (n + 1))) (T AA AB : ℕ) (hT : history.length ≤ T)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ AA)
    (hB : ∀ field, binaryWordWidth (cfg.capsB field + 1) ≤ AB)
    (epsilonA epsilonB : ℚ) (heA : 0 < epsilonA) (heB : 0 < epsilonB) (K : ℕ) :
    ImplicitTrainingTransition.bitBudget (c.compactPreparedA cfg history) (c.compactPreparedB cfg history) c.values epsilonA epsilonB K ≤
      c.compactTransitionSeedCap T AA AB epsilonA epsilonB K := by
  unfold ImplicitTrainingTransition.bitBudget compactTransitionSeedCap
  exact Nat.add_le_add_right (Nat.add_le_add (c.compactPreparedA_seedCap cfg history T AA hT hA epsilonA heA)
    (c.compactPreparedB_seedCap cfg history T AB hT hB epsilonB heB)) _

def compactHorizonSeedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (T AA AB : ℕ) (accuracy : ℚ) : ℕ :=
  c.compactTransitionSeedCap T AA AB (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
    (adaptiveFieldPrecision accuracy T)

theorem compactHorizon_seedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (T AA AB : ℕ) (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ AA)
    (hB : ∀ field, binaryWordWidth (cfg.capsB field + 1) ≤ AB) (accuracy : ℚ) (ha : 0 < accuracy) :
    ∀ history : List (RawObservation (n + 1)), history.length < T →
      ImplicitTrainingTransition.bitBudget (c.compactPreparedA cfg history) (c.compactPreparedB cfg history) c.values
        (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T) (adaptiveFieldPrecision accuracy T) ≤
          c.compactHorizonSeedCap T AA AB accuracy := by
  intro history hLength
  exact c.compactTransition_seedCap cfg history T AA AB hLength.le hA hB _ _
    (adaptiveDrawTolerance_positive accuracy ha T) (adaptiveDrawTolerance_positive accuracy ha T) _

end ProductSecurityTrainer
end Blotto
