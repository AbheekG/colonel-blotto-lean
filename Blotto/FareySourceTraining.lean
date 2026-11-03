import Blotto.FareyImplicitTrainer
import Blotto.RoundedImplicitTree

/-! The retained R127 candidate/response code universes give a concrete native
finite security trainer. Its quantile order, entropy, learning horizon and seed
cap are computed from source parameters; decoder, code-width and entropy
certificates are derived. Original-game scaling/comparator compilation,
continuous certification and complete execution prices remain separate. -/

namespace Blotto.FareySourceTraining
open Farey
open scoped BigOperators

structure Input (fields : ℕ) where
  q : ℕ
  q_positive : 0 < q
  scaleA : Fin fields → ℚ
  scaleB : Fin fields → ℚ
  scaleA_nonnegative : ∀ field, 0 ≤ scaleA field
  scaleB_nonnegative : ∀ field, 0 ≤ scaleB field
  budgetA : ℚ
  budgetB : ℚ
  budgetA_positive : 0 < budgetA
  budgetB_positive : 0 < budgetB
  values : RationalFieldSelector fields

def quantileCount (epsilon : ℚ) : ℕ := rationalFactorCeiling (64 / epsilon)

theorem quantileCount_guard (epsilon : ℚ) (he : 0 < epsilon) :
    64 ≤ (quantileCount epsilon : ℚ) * epsilon := by
  have hc := rationalFactorCeiling_bound (64 / epsilon) (by positivity)
  exact (div_le_iff₀ he).mp hc

def Input.width {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : ℕ :=
  8 + 2 * binaryWordWidth input.q +
    2 * sourceExponent (n + 1) (quantileCount epsilon) * binaryWordWidth (n + 3)

def Input.entropy {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : ℚ :=
  ((2 * (n + 1) * input.width epsilon : ℕ) : ℚ)

def Input.base {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : ProductSecurityTrainer (n + 1) :=
  FareyImplicitTrainer.create
    (sourceCandidateUniverse input.q (n + 1) (quantileCount epsilon) input.q_positive)
    (sourceResponseUniverse input.q (n + 1) (quantileCount epsilon) input.q_positive (by omega))
    input.scaleA input.scaleB input.scaleA_nonnegative input.scaleB_nonnegative
    input.budgetA input.budgetB input.budgetA_positive.le input.budgetB_positive.le input.values
    (1/8) (1/8) (by norm_num) (by norm_num)

def Input.baseConfig {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : (input.base epsilon).ImplicitCodeConfig :=
  FareyImplicitTrainer.config
    (sourceCandidateUniverse input.q (n + 1) (quantileCount epsilon) input.q_positive)
    (sourceResponseUniverse input.q (n + 1) (quantileCount epsilon) input.q_positive (by omega))
    input.scaleA input.scaleB input.scaleA_nonnegative input.scaleB_nonnegative
    input.budgetA input.budgetB input.budgetA_positive.le input.budgetB_positive.le input.values
    (1/8) (1/8) (by norm_num) (by norm_num)

theorem source_widths {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) :
    (∀ field, binaryWordWidth ((input.baseConfig epsilon).capsA field + 1) ≤ input.width epsilon) ∧
      (∀ field, binaryWordWidth ((input.baseConfig epsilon).capsB field + 1) ≤ input.width epsilon) := by
  have hw := sourceCode_word_bound input.q (n + 1) (quantileCount epsilon) input.q_positive
  exact ⟨fun _ => hw, fun _ => hw⟩

theorem entropy_nonnegative {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : 0 ≤ input.entropy epsilon := by
  unfold Input.entropy
  positivity

theorem source_entropy_bound {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) :
    Real.log (input.base epsilon).actionsA + Real.log (input.base epsilon).actionsB ≤ (input.entropy epsilon : ℝ) := by
  let c := input.base epsilon
  let N := rankCap (sourceOrder input.q (n + 1) (quantileCount epsilon)) + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hWidth : binaryWordWidth N ≤ input.width epsilon :=
    sourceCode_word_bound input.q (n + 1) (quantileCount epsilon) input.q_positive
  have hLog : Real.log N ≤ (input.width epsilon : ℝ) :=
    (ImplicitLeafCounts.logNat_le_binaryWordWidth N hN).trans (by exact_mod_cast hWidth)
  have hA := SparseMW.feasibleEntropy_bound c.bidsA c.budgetA c.fallbackA c.fallbackA_feasible N hN (fun _ => le_rfl)
  have hB := SparseMW.feasibleEntropy_bound c.bidsB c.budgetB c.fallbackB c.fallbackB_feasible N hN (fun _ => le_rfl)
  have hALog : Real.log c.actionsA ≤ ((n + 1 : ℕ) : ℝ) * input.width epsilon :=
    hA.trans (mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg _))
  have hBLog : Real.log c.actionsB ≤ ((n + 1 : ℕ) : ℝ) * input.width epsilon :=
    hB.trans (mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg _))
  change Real.log c.actionsA + Real.log c.actionsB ≤ _
  unfold Input.entropy
  push_cast at hALog hBLog ⊢
  nlinarith

def Input.rounds {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) : ℕ :=
  ProductSecurityTrainer.trainingRounds (epsilon / 2048) epsilon (input.entropy epsilon)

def Input.trainer {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    ProductSecurityTrainer (n + 1) := (input.base epsilon).withAccuracy epsilon he

def Input.config {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) :
    (input.trainer epsilon he).ImplicitCodeConfig := (input.baseConfig epsilon).withAccuracy epsilon he

def Input.seedCap {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ) : ℕ :=
  (input.trainer epsilon he).compactHorizonSeedCap (input.rounds epsilon) (input.width epsilon) (input.width epsilon) accuracy

def Input.run {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1) (accuracy : ℚ)
    (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    List (ProductSecurityTrainer.RawObservation (n + 1)) :=
  (input.trainer epsilon he).compactScheduledRun (input.config epsilon he) (input.rounds epsilon)
    (input.width epsilon) (input.width epsilon) accuracy bits

theorem run_feasible {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) (bits : Fin (input.rounds epsilon * input.seedCap epsilon he accuracy) → Bool) :
    ∀ observation ∈ input.run epsilon he accuracy bits,
      Feasible (input.budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (input.budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) :=
  (input.trainer epsilon he).compactScheduledRun_feasible (input.config epsilon he) _ _ _ accuracy ha bits

theorem run_error {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) (test : List (ProductSecurityTrainer.RawObservation (n + 1)) → ℝ)
    (hTest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean
        (fun bits => test (input.run epsilon he accuracy bits)) -
      SparseMW.historyMean (input.trainer epsilon he).transition (input.rounds epsilon)
        (fun history => test (history.map (input.trainer epsilon he).encodeObservation))| ≤ (accuracy : ℝ) :=
  (input.trainer epsilon he).compactScheduledRun_error (input.config epsilon he) _ _ _
    (source_widths input epsilon).1 (source_widths input epsilon).2 accuracy ha test hTest

theorem run_bad_gap_bound {n : ℕ} (input : Input (n + 1)) (epsilon : ℚ) (he : 0 < epsilon ∧ epsilon ≤ 1)
    (accuracy : ℚ) (ha : 0 < accuracy) :
    (fairBitKernel (input.rounds epsilon * input.seedCap epsilon he accuracy)).mean (fun bits =>
      if (epsilon : ℝ) / 8 < (input.trainer epsilon he).rawGap (input.run epsilon he accuracy bits) then 1 else 0) ≤
        1 / 16 + (accuracy : ℝ) :=
  (input.base epsilon).withAccuracy_compactScheduled_bad_gap_bound (input.baseConfig epsilon)
    epsilon (input.entropy epsilon) accuracy he (entropy_nonnegative input epsilon) (source_entropy_bound input epsilon) ha
    (input.width epsilon) (input.width epsilon) (source_widths input epsilon).1 (source_widths input epsilon).2

end Blotto.FareySourceTraining
