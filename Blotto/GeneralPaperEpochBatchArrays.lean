import Blotto.GeneralPaperEpochCellInstructions

/-! Generate the selected epoch-end instruction lists from native local
level arrays. The cumulative-effect interface is discharged by partition
coverage/disjointness and the per-round cached-cell loss semantics.
-/
namespace Blotto.GeneralPaperEpochBatchArrays
open GeneralPaperEpochCellInstructions GeneralPaperIntervalBatch GeneralPaperTreeHistory
open GeneralPaperGeometricLevels GeneralPaperGeometricVariation GeneralPaperPreparedPowers
open GeneralPaperTreeEpochJoin
set_option autoImplicit false
set_option maxHeartbeats 3000000

def batches (cellCount : ℕ → ℕ) (cells : (epoch : ℕ) → Cells (cellCount epoch))
    (delta : (epoch : ℕ) → ℕ → FixedArrayTable (cellCount epoch) ℕ) (period epoch : ℕ) : List Instruction :=
  build (cells epoch) (GeneralPaperEpochLevelArray.execute (delta epoch) period).1

theorem batch_length (cellCount : ℕ → ℕ) (cells : (epoch : ℕ) → Cells (cellCount epoch))
    (delta : (epoch : ℕ) → ℕ → FixedArrayTable (cellCount epoch) ℕ) (period epoch : ℕ) :
    (batches cellCount cells delta period epoch).length=cellCount epoch := build_length _ _

theorem batch_effect (height : ℕ) (cellCount : ℕ → ℕ) (cells : (epoch : ℕ) → Cells (cellCount epoch))
    (delta : (epoch : ℕ) → ℕ → FixedArrayTable (cellCount epoch) ℕ) (period : ℕ)
    (rowIncrement : ℕ → Fin (2^height) → ℕ)
    (hCover : ∀ epoch, Covers (2^height) (cells epoch))
    (hDisjoint : ∀ epoch, GeneralPaperEpochCellInstructions.Disjoint (cells epoch))
    (hDelta : ∀ epoch t, t<period → ∀ r (i : Fin (2^height)), Contains (cells epoch) r i.val →
      (delta epoch t).read r=rowIncrement (epoch*period+t) i) (epoch : ℕ) (i : Fin (2^height)) :
    increments height (batches cellCount cells delta period) epoch i=
      levels (fun t => rowIncrement (epoch*period+t)) period i :=
  cumulative_effect (cells epoch) (delta epoch) rowIncrement (epoch*period) period
    (hCover epoch) (hDisjoint epoch) (hDelta epoch) i

theorem executed_levels (lambda k height : ℕ) (span : ℚ) (cellCount : ℕ → ℕ)
    (cells : (epoch : ℕ) → Cells (cellCount epoch))
    (delta : (epoch : ℕ) → ℕ → FixedArrayTable (cellCount epoch) ℕ)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height)
    (hCover : ∀ epoch, Covers (2^height) (cells epoch))
    (hDisjoint : ∀ epoch, GeneralPaperEpochCellInstructions.Disjoint (cells epoch))
    (hDelta : ∀ epoch t, t<(GeneralPaperTrajectoryParameters.prepare lambda k).period →
      ∀ r (i : Fin (2^height)), Contains (cells epoch) r i.val →
        (delta epoch t).read r=rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t) i)
    (epoch : ℕ) (i : Fin (2^height)) :
    GeneralPaperIntervalLevels.levelAt
      (execute (prepare lambda k) height span
        (batches cellCount cells delta (GeneralPaperTrajectoryParameters.prepare lambda k).period) epoch).node i.val=
      levels rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period) i :=
  GeneralPaperEpochTreeHistory.selected_levels (prepare lambda k) lambda k height span _ rowIncrement hSpan
    (batch_effect height cellCount cells delta _ rowIncrement hCover hDisjoint hDelta) epoch i

theorem initial_cdf (lambda k height : ℕ) (span : ℚ) (cellCount : ℕ → ℕ)
    (cells : (epoch : ℕ) → Cells (cellCount epoch))
    (delta : (epoch : ℕ) → ℕ → FixedArrayTable (cellCount epoch) ℕ)
    (rowIncrement : ℕ → Fin (2^height) → ℕ) (hSpan : span=(2:ℚ)^height) (hHeight : height≤lambda+1)
    (hCover : ∀ epoch, Covers (2^height) (cells epoch))
    (hDisjoint : ∀ epoch, GeneralPaperEpochCellInstructions.Disjoint (cells epoch))
    (hDelta : ∀ epoch t, t<(GeneralPaperTrajectoryParameters.prepare lambda k).period →
      ∀ r (i : Fin (2^height)), Contains (cells epoch) r i.val →
        (delta epoch t).read r=rowIncrement (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period+t) i)
    (hIncrement : ∀ t i, rowIncrement t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (epoch : ℕ) (hEpoch : epoch≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    let node := (execute (prepare lambda k) height span
      (batches cellCount cells delta (GeneralPaperTrajectoryParameters.prepare lambda k).period) epoch).node
    GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (GeneralPaperCachedMassJoin.base k) rowIncrement
        (epoch*(GeneralPaperTrajectoryParameters.prepare lambda k).period) (code (Nat.two_pow_pos height) i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location lambda k height node r).val))
      (2^height-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ) :=
  GeneralPaperEpochTreeHistory.selected_initial_cdf lambda k height span _ rowIncrement hSpan hHeight
    (batch_effect height cellCount cells delta _ rowIncrement hCover hDisjoint hDelta) hIncrement epoch hEpoch

end Blotto.GeneralPaperEpochBatchArrays
