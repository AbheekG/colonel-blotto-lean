import Blotto.RawImplicitSeedCap
import Blotto.RawImplicitSecurityConfidence

/-! The concrete compact raw trainer uses a source-derived horizon bit cap.
Its fresh-bit run is feasible on every path and has the retained finite-game
confidence guarantee without a next-law or history-width oracle. Ordered zero
bid codes, code-word widths, and entropy bounds are explicit; continuous-game
compilation, output certification and complete runtime are separate results. -/

namespace Blotto
open scoped Classical
namespace ProductSecurityTrainer

def compactScheduledRun {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (T AA AB : ℕ) (accuracy : ℚ)
    (bits : Fin (T * c.compactHorizonSeedCap T AA AB accuracy) → Bool) : List (RawObservation (n + 1)) :=
  c.compactNativeRun cfg (adaptiveDrawTolerance accuracy T) (adaptiveDrawTolerance accuracy T)
    (adaptiveFieldPrecision accuracy T) (c.compactHorizonSeedCap T AA AB accuracy) T bits

theorem compactScheduledRun_feasible {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (T AA AB : ℕ) (accuracy : ℚ) (ha : 0 < accuracy)
    (bits : Fin (T * c.compactHorizonSeedCap T AA AB accuracy) → Bool) :
    ∀ observation ∈ c.compactScheduledRun cfg T AA AB accuracy bits,
      Feasible (c.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (c.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) :=
  c.compactNativeRun_feasible cfg _ _ (adaptiveDrawTolerance_positive accuracy ha T)
    (adaptiveDrawTolerance_positive accuracy ha T) _ _ _ bits

theorem compactScheduledRun_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (T AA AB : ℕ) (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ AA)
    (hB : ∀ field, binaryWordWidth (cfg.capsB field + 1) ≤ AB) (accuracy : ℚ) (ha : 0 < accuracy)
    (test : List (RawObservation (n + 1)) → ℝ) (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * c.compactHorizonSeedCap T AA AB accuracy)).mean
        (fun bits => test (c.compactScheduledRun cfg T AA AB accuracy bits)) -
      SparseMW.historyMean c.transition T (fun history => test (history.map c.encodeObservation))| ≤ (accuracy : ℝ) :=
  c.compactNativeRun_scheduled_error cfg accuracy ha T _ (c.compactHorizon_seedCap cfg T AA AB hA hB accuracy ha) test hTest

theorem compactScheduledRun_bad_gap_bound {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (T AA AB : ℕ) (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ AA)
    (hB : ∀ field, binaryWordWidth (cfg.capsB field + 1) ≤ AB) (accuracy : ℚ) (ha : 0 < accuracy) (threshold : ℝ) :
    (fairBitKernel (T * c.compactHorizonSeedCap T AA AB accuracy)).mean (fun bits =>
      if threshold < c.rawGap (c.compactScheduledRun cfg T AA AB accuracy bits) then 1 else 0) ≤
        c.badGapMean T threshold + (accuracy : ℝ) :=
  c.compactNativeRun_bad_gap_bound cfg accuracy ha T _ (c.compactHorizon_seedCap cfg T AA AB hA hB accuracy ha) threshold

def ImplicitCodeConfig.withAccuracy {m : ℕ} {c : ProductSecurityTrainer m} (cfg : c.ImplicitCodeConfig)
    (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) : (c.withAccuracy epsilon he).ImplicitCodeConfig where
  capsA := cfg.capsA
  capsB := cfg.capsB
  sizesA := cfg.sizesA
  sizesB := cfg.sizesB
  orderedA := cfg.orderedA
  orderedB := cfg.orderedB
  zeroA := cfg.zeroA
  zeroB := cfg.zeroB

theorem withAccuracy_compactScheduled_bad_gap_bound {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (epsilon entropy accuracy : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (hJ : 0 ≤ entropy)
    (hEntropy : Real.log c.actionsA + Real.log c.actionsB ≤ (entropy : ℝ)) (ha : 0 < accuracy)
    (AA AB : ℕ) (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ AA)
    (hB : ∀ field, binaryWordWidth (cfg.capsB field + 1) ≤ AB) :
    (fairBitKernel (trainingRounds (epsilon / 2048) epsilon entropy *
      (c.withAccuracy epsilon he).compactHorizonSeedCap (trainingRounds (epsilon / 2048) epsilon entropy) AA AB accuracy)).mean
      (fun bits => if (epsilon : ℝ) / 8 < (c.withAccuracy epsilon he).rawGap
        ((c.withAccuracy epsilon he).compactScheduledRun (cfg.withAccuracy epsilon he)
          (trainingRounds (epsilon / 2048) epsilon entropy) AA AB accuracy bits) then 1 else 0) ≤
            1 / 16 + (accuracy : ℝ) := by
  have hn := (c.withAccuracy epsilon he).compactScheduledRun_bad_gap_bound (cfg.withAccuracy epsilon he)
    (trainingRounds (epsilon / 2048) epsilon entropy) AA AB hA hB accuracy ha ((epsilon : ℝ) / 8)
  exact hn.trans (add_le_add (c.withAccuracy_bad_gap_bound epsilon entropy he hJ hEntropy) (le_refl (accuracy : ℝ)))

end ProductSecurityTrainer
end Blotto
