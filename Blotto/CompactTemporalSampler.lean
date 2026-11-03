import Blotto.TemporalSuffixKernel
import Blotto.RawImplicitSeedCap

/-! A fixed-history temporal draw chooses a bounded fair-bit uniform time,
reconstructs that proper suffix's compact Gibbs sampler and draws one whole
feasible rational row. The source-derived cap bounds every chosen suffix;
unused row bits are ignored. All bounded-test error is row tolerance plus the
time rejection tail. Support enumeration is only a proof representation.
Preparation, suffix access, arithmetic and complete machine prices remain
separate from this executable finite-seed sampling contract. -/

namespace Blotto.ProductSecurityTrainer
open ImplicitLeafCounts
open scoped BigOperators Classical

def temporalRowSeedCap {n : ℕ} (_c : ProductSecurityTrainer (n + 1))
    (past : List (RawObservation (n + 1))) (A : ℕ) (error : ℚ) : ℕ :=
  compactLeafSeedCap n past.length A error

def temporalSeedCap {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (past : List (RawObservation (n + 1))) (A : ℕ) (error : ℚ) (timeAttempts : ℕ) : ℕ :=
  timeAttempts * UniformNatRejection.width past.length + c.temporalRowSeedCap past A error

def temporalDrawAt {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (A : ℕ) (error : ℚ)
    (time : Fin past.length) (bits : Fin (c.temporalRowSeedCap past A error) → Bool) : Fin (n + 1) → ℚ :=
  let prepared := c.compactPreparedA cfg (temporalSuffix past time)
  if hWidth : prepared.bitBudget error ≤ c.temporalRowSeedCap past A error then
    prepared.sample error (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt hWidth⟩)
  else fun _ => 0

theorem temporalDrawAt_width {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (A : ℕ)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ A)
    (error : ℚ) (he : 0 < error) (time : Fin past.length) :
    (c.compactPreparedA cfg (temporalSuffix past time)).bitBudget error ≤
      c.temporalRowSeedCap past A error :=
  c.compactPreparedA_seedCap cfg _ past.length A (temporalSuffix_length past time) hA error he

theorem temporalDrawAt_feasible {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (A : ℕ) (error : ℚ) (he : 0 < error)
    (time : Fin past.length) (bits : Fin (c.temporalRowSeedCap past A error) → Bool) :
    Feasible (c.budgetA : ℝ) (fun field => (c.temporalDrawAt cfg past A error time bits field : ℝ)) := by
  unfold temporalDrawAt
  split
  · rename_i hWidth
    have h := (c.compactPreparedA cfg (temporalSuffix past time)).sample_feasible error he
      (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt hWidth⟩)
    rw [c.compactPreparedA_budget] at h
    exact h
  · simpa only [Rat.cast_zero] using
      feasible_zero (by exact_mod_cast c.budgetA_nonnegative : (0 : ℝ) ≤ c.budgetA)

theorem temporalDrawAt_mean_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (A : ℕ)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ A)
    (error : ℚ) (he : 0 < error) (time : Fin past.length)
    (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |(fairBitKernel (c.temporalRowSeedCap past A error)).mean
        (fun bits => test (c.temporalDrawAt cfg past A error time bits)) -
      (c.rawPreparedA (temporalSuffix past time)).rationalTargetKernel.mean test| ≤ (error : ℝ) := by
  have hFit := c.temporalDrawAt_width cfg past A hA error he time
  unfold temporalDrawAt
  simp only [hFit, dite_true]
  rw [fairBitKernel_prefix_mean _ _ hFit
    (fun bits => test ((c.compactPreparedA cfg (temporalSuffix past time)).sample error bits))]
  exact c.compactPreparedA_native_mean_error cfg _ error he test hTest

def temporalSample {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ) (error : ℚ)
    (timeAttempts : ℕ) (bits : Fin (c.temporalSeedCap past A error timeAttempts) → Bool) : Fin (n + 1) → ℚ :=
  let R := timeAttempts * UniformNatRejection.width past.length
  let B := c.temporalRowSeedCap past A error
  let time := UniformNatRejection.sample past.length hPast timeAttempts (firstBitBlock R B bits)
  c.temporalDrawAt cfg past A error time (secondBitBlock R B bits)

theorem temporalSample_feasible {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ)
    (error : ℚ) (he : 0 < error) (timeAttempts : ℕ)
    (bits : Fin (c.temporalSeedCap past A error timeAttempts) → Bool) :
    Feasible (c.budgetA : ℝ) (fun field => (c.temporalSample cfg past hPast A error timeAttempts bits field : ℝ)) :=
  c.temporalDrawAt_feasible cfg past A error he _ _

noncomputable def temporalTimeKernel {n : ℕ} (_c : ProductSecurityTrainer (n + 1))
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (timeAttempts : ℕ) :
    BoundedExpectationKernel (Fin past.length) :=
  (fairBitKernel (timeAttempts * UniformNatRejection.width past.length)).map
    (UniformNatRejection.sample past.length hPast timeAttempts)

noncomputable def temporalAtKernel {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (A : ℕ) (error : ℚ) (time : Fin past.length) :
    BoundedExpectationKernel (Fin (n + 1) → ℚ) :=
  (fairBitKernel (c.temporalRowSeedCap past A error)).map (c.temporalDrawAt cfg past A error time)

theorem temporalSample_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ) (error : ℚ)
    (timeAttempts : ℕ) (test : (Fin (n + 1) → ℚ) → ℝ) :
    (fairBitKernel (c.temporalSeedCap past A error timeAttempts)).mean
      (fun bits => test (c.temporalSample cfg past hPast A error timeAttempts bits)) =
    ((c.temporalTimeKernel past hPast timeAttempts).bind
      (c.temporalAtKernel cfg past A error)).mean test :=
  fairBitKernel_blocks _ _ (fun timeBits rowBits => test (c.temporalDrawAt cfg past A error
    (UniformNatRejection.sample past.length hPast timeAttempts timeBits) rowBits))

theorem temporalSample_mean_error {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (cfg : c.ImplicitCodeConfig)
    (past : List (RawObservation (n + 1))) (hPast : 0 < past.length) (A : ℕ)
    (hA : ∀ field, binaryWordWidth (cfg.capsA field + 1) ≤ A)
    (error : ℚ) (he : 0 < error) (timeAttempts : ℕ)
    (test : (Fin (n + 1) → ℚ) → ℝ) (hTest : ∀ row, 0 ≤ test row ∧ test row ≤ 1) :
    |(fairBitKernel (c.temporalSeedCap past A error timeAttempts)).mean
        (fun bits => test (c.temporalSample cfg past hPast A error timeAttempts bits)) -
      (c.averageLawA past hPast).rowKernel.mean test| ≤ (error : ℝ) + 1 / (2 : ℝ) ^ timeAttempts := by
  have hTime : (c.temporalTimeKernel past hPast timeAttempts).Close
      (UniformNatRejection.targetKernel past.length hPast) (1 / (2 : ℝ) ^ timeAttempts) :=
    UniformNatRejection.sample_mean_error past.length hPast timeAttempts
  have hAt : ∀ time, (c.temporalAtKernel cfg past A error time).Close
      (c.rawPreparedA (temporalSuffix past time)).rationalTargetKernel (error : ℝ) := by
    intro time f hf
    exact c.temporalDrawAt_mean_error cfg past A hA error he time f hf
  have h := BoundedExpectationKernel.bind_close _ _ _ _ _ _ hTime hAt test hTest
  rw [← c.temporalSample_mean cfg past hPast A error timeAttempts test] at h
  change |(fairBitKernel (c.temporalSeedCap past A error timeAttempts)).mean
      (fun bits => test (c.temporalSample cfg past hPast A error timeAttempts bits)) -
    (UniformNatRejection.targetKernel past.length hPast).mean
      (fun time => (c.rawPreparedA (temporalSuffix past time)).rationalTargetKernel.mean test)| ≤ _ at h
  rw [← c.temporal_rowKernel_suffix_mean past hPast test] at h
  simpa only [add_comm] using h

end Blotto.ProductSecurityTrainer
