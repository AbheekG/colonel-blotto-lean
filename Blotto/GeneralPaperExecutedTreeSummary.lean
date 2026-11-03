import Blotto.GeneralPaperTreeHistoryWork

/-! Unit-bounded batch specialization of the executed tree summary. Its
cache-validity, code-level-history and path-cap certificates are derived.
The selected epoch-end schedule, with cumulative cell increments, is joined
separately in GeneralPaperEpochTreeHistory.
-/
namespace Blotto.GeneralPaperExecutedTreeSummary
open GeneralPaperPreparedPowers GeneralPaperIntervalBatch GeneralPaperTreeHistory
open GeneralPaperTreeEpochJoin GeneralPaperGeometricLevels GeneralPaperGeometricVariation
open GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem initial_cdf (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (hHeight : height≤lambda+1) (start : ℕ)
    (hStart : start≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ t i, increments height batches t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    let node := (execute (prepare lambda k) height span batches start).node
    GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) (increments height batches) start (code (Nat.two_pow_pos height) i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location lambda k height node r).val))
      (2^height-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  exact initial_history_close lambda k height start _ (increments height batches) hHeight
    (execute_valid lambda k height span batches hSpan start hStart hIncrement)
    (execute_levels (prepare lambda k) height span batches hSpan start) hStart hIncrement

theorem epoch_cdf (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (hHeight : height≤lambda+1) (start count : ℕ)
    (hStart : start≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ t i, increments height batches t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increments height batches t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increments height batches t (code (Nat.two_pow_pos height) i)):ℝ)) (2^height-1)≤4)
    (prefixCount : ℕ) (hPrefix : prefixCount≤2^height) :
    let node := (execute (prepare lambda k) height span batches start).node
    |prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) (increments height batches) (start+count)
      (code (Nat.two_pow_pos height) i)) prefixCount-
      GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location lambda k height node r).val)
        (fun r => (GeneralPaperDyadicFloat.value (query (prepare lambda k)
          (levels (fun t => increments height batches (start+t)) count (location lambda k height node r))).number:ℝ)) prefixCount/
        (∑ r, (GeneralPaperDyadicFloat.value (query (prepare lambda k)
          (levels (fun t => increments height batches (start+t)) count (location lambda k height node r))).number:ℝ))|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  exact epoch_cdf_error lambda k height start count _ (increments height batches) hHeight
    (execute_valid lambda k height span batches hSpan start hStart hIncrement)
    (execute_levels (prepare lambda k) height span batches hSpan start) hStart hIncrement hCount hMagnitude hVariation prefixCount hPrefix

end Blotto.GeneralPaperExecutedTreeSummary
