import Blotto.GeneralPaperOccurrenceUpdates

/-! Actual unsigned cell batches across epochs refine the global full-code
learner. The epoch/local time map is constructed by quotient/remainder.
Prefix arrays and epoch summaries remain inputs here; their coupled adaptive
generation is a separate source invariant. No cell-effect oracle is assumed.
-/
namespace Blotto.GeneralPaperUnsignedCellHistory
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperGeometricLevels GeneralPaperPreparedPowers GeneralPaperTreeHistory
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem epoch_index (period epoch localTime : ℕ) (hPeriod : 0<period) (hLocal : localTime<period) :
    (epoch*period+localTime)/period=epoch := by
  rw [Nat.add_comm (epoch*period) localTime,Nat.add_mul_div_right _ _ hPeriod,Nat.div_eq_of_lt hLocal,Nat.zero_add]

theorem local_index (period epoch localTime : ℕ) (hLocal : localTime<period) :
    (epoch*period+localTime)%period=localTime := by
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,Nat.zero_add,Nat.mod_eq_of_lt hLocal]

def increment (k U period : ℕ) (response : Bool) (cdfSummary signedSummary : ℕ → Summary k)
    (cdfPrefix signedPrefix : ℕ → ℕ → Prefix k) (time : ℕ) (i : Fin U) : ℕ :=
  GeneralPaperQueryLossCounts.increment k response
    (GeneralPaperNativeLossReference.reference k U (cdfSummary (time/period)) (signedSummary (time/period))
      (cdfPrefix (time/period) (time%period)) (signedPrefix (time/period) (time%period)) i.val)

theorem increment_at (k U period : ℕ) (response : Bool) (cdfSummary signedSummary : ℕ → Summary k)
    (cdfPrefix signedPrefix : ℕ → ℕ → Prefix k) (hPeriod : 0<period) (epoch localTime : ℕ) (hLocal : localTime<period) (i : Fin U) :
    increment k U period response cdfSummary signedSummary cdfPrefix signedPrefix (epoch*period+localTime) i=
      GeneralPaperQueryLossCounts.increment k response
        (GeneralPaperNativeLossReference.reference k U (cdfSummary epoch) (signedSummary epoch)
          (cdfPrefix epoch localTime) (signedPrefix epoch localTime) i.val) := by
  unfold increment
  rw [epoch_index period epoch localTime hPeriod hLocal,local_index period epoch localTime hLocal]

def batches (k U period : ℕ) (response : Bool) (optionCount : ℕ → ℕ)
    (cdfSummary signedSummary : ℕ → Summary k) (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ)
    (cdfPrefix signedPrefix : ℕ → ℕ → Prefix k) (epoch : ℕ) : List GeneralPaperIntervalBatch.Instruction :=
  let plan := GeneralPaperUnsignedCellUpdates.prepare k U (cdfSummary epoch) (signedSummary epoch) (options epoch)
  GeneralPaperEpochCellInstructions.build plan.partition.intervals
    (GeneralPaperDeltaAccumulation.run (fun t => GeneralPaperUnsignedCellUpdates.delta k response
      (cdfPrefix epoch t) (signedPrefix epoch t) plan) period).1

theorem batches_eq (k U period : ℕ) (response : Bool) (optionCount : ℕ → ℕ)
    (cdfSummary signedSummary : ℕ → Summary k) (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ)
    (cdfPrefix signedPrefix : ℕ → ℕ → Prefix k) (epoch : ℕ) :
    batches k U period response optionCount cdfSummary signedSummary options cdfPrefix signedPrefix epoch=
      GeneralPaperUnsignedCellUpdates.batch k response (cdfPrefix epoch) (signedPrefix epoch)
        (GeneralPaperUnsignedCellUpdates.prepare k U (cdfSummary epoch) (signedSummary epoch) (options epoch)) period := by
  unfold batches GeneralPaperUnsignedCellUpdates.batch
  dsimp only
  rw [GeneralPaperDeltaAccumulation.data_eq]

theorem batch_effect (k U period : ℕ) (response : Bool) (optionCount : ℕ → ℕ)
    (cdfSummary signedSummary : ℕ → Summary k) (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ)
    (cdfPrefix signedPrefix : ℕ → ℕ → Prefix k) (hPeriod : 0<period)
    (hCDFMono : ∀ e, Monotone (cdfSummary e).read) (hSignedMono : ∀ e, Monotone (signedSummary e).read)
    (hCDFCodes : ∀ e a, (cdfSummary e).read a<U) (hSignedCodes : ∀ e a, (signedSummary e).read a<2*U) (epoch : ℕ) (i : Fin U) :
    GeneralPaperIntervalBatch.effect (batches k U period response optionCount cdfSummary signedSummary options cdfPrefix signedPrefix epoch) i.val=
      levels (fun t => increment k U period response cdfSummary signedSummary cdfPrefix signedPrefix (epoch*period+t)) period i := by
  rw [batches_eq,GeneralPaperUnsignedCellUpdates.cumulative_effect k U response (cdfSummary epoch) (signedSummary epoch)
    (options epoch) (cdfPrefix epoch) (signedPrefix epoch) (hCDFMono epoch) (hSignedMono epoch) (hCDFCodes epoch) (hSignedCodes epoch)]
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t ht
  exact (increment_at k U period response cdfSummary signedSummary cdfPrefix signedPrefix hPeriod epoch t ht i).symm

theorem selected_period_positive (lambda k : ℕ) : 0<(GeneralPaperTrajectoryParameters.prepare lambda k).period := by
  rw [GeneralPaperTrajectoryParameters.period_power]
  exact Nat.two_pow_pos _

theorem tree_levels (lambda k height : ℕ) (span : ℚ) (response : Bool) (optionCount : ℕ → ℕ)
    (cdfSummary signedSummary : ℕ → Summary k) (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ)
    (cdfPrefix signedPrefix : ℕ → ℕ → Prefix k) (hSpan : span=(2:ℚ)^height)
    (hCDFMono : ∀ e, Monotone (cdfSummary e).read) (hSignedMono : ∀ e, Monotone (signedSummary e).read)
    (hCDFCodes : ∀ e a, (cdfSummary e).read a<2^height) (hSignedCodes : ∀ e a, (signedSummary e).read a<2*(2^height))
    (epoch : ℕ) (i : Fin (2^height)) :
    let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
    GeneralPaperIntervalLevels.levelAt
      (execute (prepare lambda k) height span
        (batches k (2^height) period response optionCount cdfSummary signedSummary options cdfPrefix signedPrefix) epoch).node i.val=
      levels (increment k (2^height) period response cdfSummary signedSummary cdfPrefix signedPrefix) (epoch*period) i := by
  exact GeneralPaperEpochTreeHistory.selected_levels (prepare lambda k) lambda k height span _ _ hSpan
    (batch_effect k (2^height) _ response optionCount cdfSummary signedSummary options cdfPrefix signedPrefix
      (selected_period_positive lambda k) hCDFMono hSignedMono hCDFCodes hSignedCodes) epoch i

theorem increment_bound (k U period : ℕ) (response : Bool) (cdfSummary signedSummary : ℕ → Summary k)
    (cdfValues signedValues : ℕ → ℕ → Summary k) (hCDF : ∀ e t, 0<∑ r, (cdfValues e t).read r)
    (hSigned : ∀ e t, 0<∑ r, (signedValues e t).read r) (time : ℕ) (i : Fin U) :
    increment k U period response cdfSummary signedSummary
      (fun e t => GeneralPaperEpochPrefixArray.build (cdfValues e t))
      (fun e t => GeneralPaperEpochPrefixArray.build (signedValues e t)) time i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  GeneralPaperQueryLossCounts.increment_bound k response _
    (GeneralPaperNativeLossReference.reference_bounds k U _ _ _ _ (hCDF _ _) (hSigned _ _) _)

theorem tree_valid (lambda k height : ℕ) (span : ℚ) (response : Bool) (optionCount : ℕ → ℕ)
    (cdfSummary signedSummary : ℕ → Summary k) (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ)
    (cdfValues signedValues : ℕ → ℕ → Summary k) (hSpan : span=(2:ℚ)^height)
    (hCDFMono : ∀ e, Monotone (cdfSummary e).read) (hSignedMono : ∀ e, Monotone (signedSummary e).read)
    (hCDFCodes : ∀ e a, (cdfSummary e).read a<2^height) (hSignedCodes : ∀ e a, (signedSummary e).read a<2*(2^height))
    (hCDF : ∀ e t, 0<∑ r, (cdfValues e t).read r) (hSigned : ∀ e t, 0<∑ r, (signedValues e t).read r)
    (epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
    GeneralPaperIntervalCache.Valid lambda k
      (execute (prepare lambda k) height span
        (batches k (2^height) period response optionCount cdfSummary signedSummary options
          (fun e t => GeneralPaperEpochPrefixArray.build (cdfValues e t))
          (fun e t => GeneralPaperEpochPrefixArray.build (signedValues e t))) epoch).node := by
  exact GeneralPaperEpochTreeHistory.selected_valid lambda k height span _ _ hSpan
    (batch_effect k (2^height) _ response optionCount cdfSummary signedSummary options _ _
      (selected_period_positive lambda k) hCDFMono hSignedMono hCDFCodes hSignedCodes)
    (increment_bound k (2^height) _ response cdfSummary signedSummary cdfValues signedValues hCDF hSigned) epoch hEpoch

end Blotto.GeneralPaperUnsignedCellHistory
