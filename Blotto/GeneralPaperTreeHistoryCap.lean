import Blotto.GeneralPaperExecutedTreeSummary

/-! A final aggregate level cap controls all preceding batches. This handles
epoch-end cell updates, whose amounts may accumulate many learner rounds.
No artificial per-cell reserve or per-round tree update is required.
-/
namespace Blotto.GeneralPaperTreeHistoryCap
open GeneralPaperPreparedPowers GeneralPaperIntervalBatch GeneralPaperTreeHistory
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGeometricLevels
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem levels_monotone {n : ℕ} (increment : ℕ → Fin n → ℕ) (i : Fin n) :
    Monotone (fun t => levels increment t i) := by
  apply monotone_nat_of_le_succ
  intro t
  dsimp only [levels]
  omega

theorem execute_valid_from_cap (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t : ℕ)
    (hFinal : ∀ i, levels (increments height batches) t i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    Valid lambda k (execute (prepare lambda k) height span batches t).node := by
  revert hFinal
  induction t with
  | zero => intro _; exact Nat.zero_le _
  | succ t ih =>
    intro hFinal
    have hPrevious := ih (fun i => (levels_monotone (increments height batches) i (Nat.le_succ t)).trans (hFinal i))
    dsimp only [execute]
    apply GeneralPaperIntervalBatch.run_valid lambda k height span _ (batches t) hSpan hPrevious
    intro i hi
    rw [execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩]
    exact hFinal ⟨i,hi⟩

theorem execute_path_from_cap (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t : ℕ)
    (hFinal : ∀ i, levels (increments height batches) t i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (execute (prepare lambda k) height span batches t).node := by
  intro i hi
  simpa only [Nat.zero_add,execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩] using hFinal ⟨i,hi⟩

theorem prefix_valid_from_cap (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t n : ℕ)
    (hFinal : ∀ i, levels (increments height batches) (t+1) i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    Valid lambda k (GeneralPaperIntervalBatch.run (prepare lambda k) height span
      (execute (prepare lambda k) height span batches t).node ((batches t).take n)).node := by
  have hPrevious := execute_valid_from_cap lambda k height span batches hSpan t
    (fun i => (levels_monotone (increments height batches) i (Nat.le_succ t)).trans (hFinal i))
  apply GeneralPaperIntervalBatchBounds.prefix_valid lambda k height span _ (batches t) hSpan hPrevious _ n
  intro i hi
  rw [execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩]
  exact hFinal ⟨i,hi⟩

end Blotto.GeneralPaperTreeHistoryCap
