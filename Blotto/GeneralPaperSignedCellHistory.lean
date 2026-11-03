import Blotto.GeneralPaperUnsignedCellHistory

/-! Executed signed batches refine one full signed-alphabet learner across
epochs. Bids come from their actual cached option indices. Prefix generation,
row optimization and the selected root-span join remain separate obligations.
-/
namespace Blotto.GeneralPaperSignedCellHistory
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperGeometricLevels GeneralPaperPreparedPowers GeneralPaperTreeHistory
open GeneralPaperUnsignedCellHistory (epoch_index local_index selected_period_positive)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def increment (k U period : ℕ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (preparedPrefix : ℕ → ℕ → Prefix k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (time code : ℕ) : ℕ :=
  let epoch := time/period
  let localTime := time%period
  GeneralPaperSignedUpdateReference.increment k U (options epoch |>.read (selection epoch localTime))
    (summary epoch) (preparedPrefix epoch localTime) code

theorem increment_at (k U period : ℕ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (preparedPrefix : ℕ → ℕ → Prefix k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (hPeriod : 0<period)
    (epoch localTime : ℕ) (hLocal : localTime<period) (code : ℕ) :
    increment k U period optionCount summary options preparedPrefix selection (epoch*period+localTime) code=
      GeneralPaperSignedUpdateReference.increment k U ((options epoch).read (selection epoch localTime))
        (summary epoch) (preparedPrefix epoch localTime) code := by
  unfold increment
  rw [epoch_index period epoch localTime hPeriod hLocal,local_index period epoch localTime hLocal]

def batches (k U period : ℕ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (preparedPrefix : ℕ → ℕ → Prefix k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (epoch : ℕ) : List GeneralPaperIntervalBatch.Instruction :=
  let plan := GeneralPaperSignedCellUpdates.prepare k U (summary epoch) (options epoch)
  GeneralPaperEpochCellInstructions.build plan.partition.intervals
    (GeneralPaperDeltaAccumulation.run (fun t => GeneralPaperSignedCellUpdates.delta k U
      ((options epoch).read (selection epoch t)) (preparedPrefix epoch t) plan) period).1

theorem batches_eq (k U period : ℕ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (preparedPrefix : ℕ → ℕ → Prefix k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (epoch : ℕ) :
    batches k U period optionCount summary options preparedPrefix selection epoch=
      GeneralPaperSignedCellUpdates.batch k U (fun t => (options epoch).read (selection epoch t)) (preparedPrefix epoch)
        (GeneralPaperSignedCellUpdates.prepare k U (summary epoch) (options epoch)) period := by
  unfold batches GeneralPaperSignedCellUpdates.batch
  dsimp only
  rw [GeneralPaperDeltaAccumulation.data_eq]

theorem batch_effect (n k U period : ℕ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (preparedPrefix : ℕ → ℕ → Prefix k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (hPeriod : 0<period) (hAlphabet : n=2*U)
    (hMono : ∀ e, Monotone (summary e).read) (hCodes : ∀ e a, (summary e).read a<U)
    (hBids : ∀ e q, (options e).read q<U) (epoch : ℕ) (i : Fin n) :
    GeneralPaperIntervalBatch.effect (batches k U period optionCount summary options preparedPrefix selection epoch) i.val=
      levels (fun t (a : Fin n) => increment k U period optionCount summary options preparedPrefix selection (epoch*period+t) a.val) period i := by
  let code : Fin (2*U) := ⟨i.val,by rw [←hAlphabet]; exact i.isLt⟩
  rw [batches_eq]
  have he := GeneralPaperSignedCellUpdates.cumulative_effect k U (summary epoch) (options epoch) (preparedPrefix epoch)
    (selection epoch) (hMono epoch) (hCodes epoch) (hBids epoch) period code
  calc
    _ = levels (fun t (a : Fin (2*U)) => GeneralPaperSignedUpdateReference.increment k U
          ((options epoch).read (selection epoch t)) (summary epoch) (preparedPrefix epoch t) a.val) period code := he
    _ = _ := by
      apply GeneralPaperEpochLevelArray.levels_agree
      intro t ht
      exact (increment_at k U period optionCount summary options preparedPrefix selection hPeriod epoch t ht i.val).symm

theorem tree_levels (lambda k U height : ℕ) (span : ℚ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (preparedPrefix : ℕ → ℕ → Prefix k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (hSpan : span=(2:ℚ)^height) (hAlphabet : 2^height=2*U)
    (hMono : ∀ e, Monotone (summary e).read) (hCodes : ∀ e a, (summary e).read a<U) (hBids : ∀ e q, (options e).read q<U)
    (epoch : ℕ) (i : Fin (2^height)) :
    let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
    GeneralPaperIntervalLevels.levelAt (execute (prepare lambda k) height span
      (batches k U period optionCount summary options preparedPrefix selection) epoch).node i.val=
      levels (fun t (a : Fin (2^height)) => increment k U period optionCount summary options preparedPrefix selection t a.val) (epoch*period) i := by
  let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
  exact GeneralPaperEpochTreeHistory.selected_levels (prepare lambda k) lambda k height span
    (batches k U period optionCount summary options preparedPrefix selection)
    (fun t (a : Fin (2^height)) => increment k U period optionCount summary options preparedPrefix selection t a.val) hSpan
    (batch_effect (2^height) k U _ optionCount summary options preparedPrefix selection
      (selected_period_positive lambda k) hAlphabet hMono hCodes hBids) epoch i

theorem increment_bound (k U period : ℕ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (values : ℕ → ℕ → Summary k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (hTotal : ∀ e t, 0<∑ r, (values e t).read r) (time code : ℕ) :
    increment k U period optionCount summary options (fun e t => GeneralPaperEpochPrefixArray.build (values e t)) selection time code≤
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  GeneralPaperRoundedLosses.signed_increment_bound _ _
    (GeneralPaperRankedCDFQuery.reference_count_bound k _ _ (hTotal _ _) _) _ _

theorem tree_valid (lambda k U height : ℕ) (span : ℚ) (optionCount : ℕ → ℕ) (summary : ℕ → Summary k)
    (options : (epoch : ℕ) → FixedArrayTable (optionCount epoch) ℕ) (values : ℕ → ℕ → Summary k)
    (selection : (epoch : ℕ) → ℕ → Fin (optionCount epoch)) (hSpan : span=(2:ℚ)^height) (hAlphabet : 2^height=2*U)
    (hMono : ∀ e, Monotone (summary e).read) (hCodes : ∀ e a, (summary e).read a<U) (hBids : ∀ e q, (options e).read q<U)
    (hTotal : ∀ e t, 0<∑ r, (values e t).read r) (epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
    GeneralPaperIntervalCache.Valid lambda k (execute (prepare lambda k) height span
      (batches k U period optionCount summary options (fun e t => GeneralPaperEpochPrefixArray.build (values e t)) selection) epoch).node := by
  let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
  let preparedPrefix := fun e t => GeneralPaperEpochPrefixArray.build (values e t)
  exact GeneralPaperEpochTreeHistory.selected_valid lambda k height span
    (batches k U period optionCount summary options preparedPrefix selection)
    (fun t (a : Fin (2^height)) => increment k U period optionCount summary options preparedPrefix selection t a.val) hSpan
    (batch_effect (2^height) k U period optionCount summary options preparedPrefix selection
      (selected_period_positive lambda k) hAlphabet hMono hCodes hBids)
    (fun t i => increment_bound k U _ optionCount summary options values selection hTotal t i.val) epoch hEpoch

end Blotto.GeneralPaperSignedCellHistory
