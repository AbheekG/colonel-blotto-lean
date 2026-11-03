import Blotto.GeneralPaperIntervalBatchBounds
import Blotto.GeneralPaperTreeEpochJoin

/-! Actual sparse tree histories, initialized uniformly and updated by each
batch's range-instruction list. Exact levels, cache validity and the global
path cap are consequences of execution. The unit-bounded specialization below
is extended to selected epoch-end batches by GeneralPaperEpochTreeHistory.
-/
namespace Blotto.GeneralPaperTreeHistory
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperPreparedPowers
open GeneralPaperIntervalBatch GeneralPaperGeometricLevels GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 3000000

def increments (height : ℕ) (batches : ℕ → List Instruction) (t : ℕ) (i : Fin (2^height)) : ℕ := effect (batches t) i.val

def execute (prepared : Prepared) (height : ℕ) (span : ℚ) (batches : ℕ → List Instruction) : ℕ → Result height
  | 0 => ⟨.uniform height 0,8,0⟩
  | t+1 =>
    let previous := execute prepared height span batches t
    let updated := GeneralPaperIntervalBatch.run prepared height span previous.node (batches t)
    ⟨updated.node,previous.work+updated.work+16,previous.visits+updated.visits⟩

theorem execute_levels (prepared : Prepared) (height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t : ℕ) (i : Fin (2^height)) :
    levelAt (execute prepared height span batches t).node i.val=levels (increments height batches) t i := by
  induction t with
  | zero => simp only [execute,levelAt,levels]
  | succ t ih =>
    dsimp only [execute]
    rw [GeneralPaperIntervalBatch.run_levels prepared height span _ (batches t) hSpan i.val i.isLt,ih]
    rfl

theorem execute_path (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t : ℕ)
    (hCount : t≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ r i, increments height batches r i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (execute (prepare lambda k) height span batches t).node := by
  intro i hi
  simp only [Nat.zero_add]
  rw [execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩]
  exact GeneralPaperPowerPrecision.local_level_bound (Nat.two_pow_pos height) lambda k t _ hCount hIncrement _

theorem execute_valid (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t : ℕ)
    (hCount : t≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ r i, increments height batches r i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    Valid lambda k (execute (prepare lambda k) height span batches t).node := by
  revert hCount
  induction t with
  | zero => intro _; exact Nat.zero_le _
  | succ t ih =>
    intro hCount
    have hPrevious := ih (by omega)
    dsimp only [execute]
    apply GeneralPaperIntervalBatch.run_valid lambda k height span _ (batches t) hSpan hPrevious
    intro i hi
    rw [execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩]
    change levels (increments height batches) (t+1) ⟨i,hi⟩≤_
    exact GeneralPaperPowerPrecision.local_level_bound (Nat.two_pow_pos height) lambda k (t+1) _ hCount hIncrement _

theorem within_round_valid (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t n : ℕ)
    (hCount : t+1≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ r i, increments height batches r i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    Valid lambda k (GeneralPaperIntervalBatch.run (prepare lambda k) height span
      (execute (prepare lambda k) height span batches t).node ((batches t).take n)).node := by
  have hPrevious := execute_valid lambda k height span batches hSpan t (by omega) hIncrement
  apply GeneralPaperIntervalBatchBounds.prefix_valid lambda k height span _ (batches t) hSpan hPrevious _ n
  intro i hi
  rw [execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩]
  change levels (increments height batches) (t+1) ⟨i,hi⟩≤_
  exact GeneralPaperPowerPrecision.local_level_bound (Nat.two_pow_pos height) lambda k (t+1) _ hCount hIncrement _

end Blotto.GeneralPaperTreeHistory
