import Blotto.GeneralPaperTreeHistoryCap

/-! The selected schedule changes the full tree only at epoch boundaries.
Each cell's cumulative local level is applied once. Grouping the learner's
round increments proves the exact full-history law, validity and summary
certificate for this schedule, including every partial epoch-end batch.
-/
namespace Blotto.GeneralPaperEpochTreeHistory
open GeneralPaperPreparedPowers GeneralPaperIntervalBatch GeneralPaperTreeHistory
open GeneralPaperTreeHistoryCap GeneralPaperIntervalCache GeneralPaperIntervalLevels
open GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperTreeEpochJoin
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem grouped_levels (height period : ℕ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*period+t)) period i)
    (epoch : ℕ) (i : Fin (2^height)) :
    levels (increments height batches) epoch i=levels rowIncrement (epoch*period) i := by
  induction epoch with
  | zero => simp only [Nat.zero_mul,levels]
  | succ epoch ih =>
    change levels (increments height batches) epoch i+increments height batches epoch i=
      levels rowIncrement ((epoch+1)*period) i
    rw [hBatch epoch i,ih,Nat.succ_mul,levels_epoch]

theorem epoch_rows_bound (lambda k epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows := by
  rw [GeneralPaperTrajectoryParameters.rows_product]
  exact Nat.mul_le_mul_right _ hEpoch

theorem selected_levels (prepared : Prepared) (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t))
        (GeneralPaperTrajectoryParameters.prepare lambda k).period i)
    (epoch : ℕ) (i : Fin (2^height)) :
    levelAt (execute prepared height span batches epoch).node i.val=
      levels rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period) i := by
  rw [execute_levels prepared height span batches hSpan epoch i,grouped_levels height _ batches rowIncrement hBatch]

theorem selected_cap (lambda k height : ℕ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t))
        (GeneralPaperTrajectoryParameters.prepare lambda k).period i)
    (hIncrement : ∀ t i, rowIncrement t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) (i : Fin (2^height)) :
    levels (increments height batches) epoch i≤GeneralPaperPowerPrecision.levelBound lambda k := by
  rw [grouped_levels height _ batches rowIncrement hBatch]
  exact GeneralPaperPowerPrecision.local_level_bound (Nat.two_pow_pos height) lambda k _ rowIncrement
    (epoch_rows_bound lambda k epoch hEpoch) hIncrement i

theorem selected_valid (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t))
        (GeneralPaperTrajectoryParameters.prepare lambda k).period i)
    (hIncrement : ∀ t i, rowIncrement t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    Valid lambda k (execute (prepare lambda k) height span batches epoch).node :=
  execute_valid_from_cap lambda k height span batches hSpan epoch
    (selected_cap lambda k height batches rowIncrement hBatch hIncrement epoch hEpoch)

theorem selected_prefix_valid (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t))
        (GeneralPaperTrajectoryParameters.prepare lambda k).period i)
    (hIncrement : ∀ t i, rowIncrement t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (epoch n : ℕ) (hEpoch : epoch+1≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    Valid lambda k (GeneralPaperIntervalBatch.run (prepare lambda k) height span
      (execute (prepare lambda k) height span batches epoch).node ((batches epoch).take n)).node :=
  prefix_valid_from_cap lambda k height span batches hSpan epoch n
    (selected_cap lambda k height batches rowIncrement hBatch hIncrement (epoch+1) hEpoch)

theorem selected_initial_cdf (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height) (hHeight : height≤lambda+1)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t))
        (GeneralPaperTrajectoryParameters.prepare lambda k).period i)
    (hIncrement : ∀ t i, rowIncrement t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    let node := (execute (prepare lambda k) height span batches epoch).node
    GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) rowIncrement
        (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period) (code (Nat.two_pow_pos height) i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location lambda k height node r).val))
      (2^height-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  exact initial_history_close lambda k height _ _ rowIncrement hHeight
    (selected_valid lambda k height span batches rowIncrement hSpan hBatch hIncrement epoch hEpoch)
    (selected_levels (prepare lambda k) lambda k height span batches rowIncrement hSpan hBatch epoch)
    (epoch_rows_bound lambda k epoch hEpoch) hIncrement

theorem selected_epoch_query (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height) (hHeight : height≤lambda+1)
    (hBatch : ∀ epoch i, increments height batches epoch i=
      levels (fun t => rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t))
        (GeneralPaperTrajectoryParameters.prepare lambda k).period i)
    (hIncrement : ∀ t i, rowIncrement t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (epoch count : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (rowIncrement t i):ℝ)|≤2)
    (hVariation : ∀ t, GeneralPaperOrderedVariation.variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (rowIncrement t (code (Nat.two_pow_pos height) i)):ℝ)) (2^height-1)≤4)
    (prefixCount : ℕ) (hPrefix : prefixCount≤2^height) :
    let node := (execute (prepare lambda k) height span batches epoch).node
    let start := epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period
    |GeneralPaperOrderedVariation.prefixMass (fun i => probability (GeneralPaperCachedMassJoin.base k) rowIncrement (start+count)
      (code (Nat.two_pow_pos height) i)) prefixCount-
      GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location lambda k height node r).val)
        (fun r => (GeneralPaperDyadicFloat.value (query (prepare lambda k)
          (levels (fun t => rowIncrement (start+t)) count (location lambda k height node r))).number:ℝ)) prefixCount/
        (∑ r, (GeneralPaperDyadicFloat.value (query (prepare lambda k)
          (levels (fun t => rowIncrement (start+t)) count (location lambda k height node r))).number:ℝ))|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  exact epoch_cdf_error lambda k height _ count _ rowIncrement hHeight
    (selected_valid lambda k height span batches rowIncrement hSpan hBatch hIncrement epoch hEpoch)
    (selected_levels (prepare lambda k) lambda k height span batches rowIncrement hSpan hBatch epoch)
    (epoch_rows_bound lambda k epoch hEpoch) hIncrement hCount hMagnitude hVariation prefixCount hPrefix

end Blotto.GeneralPaperEpochTreeHistory
