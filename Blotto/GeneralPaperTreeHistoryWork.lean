import Blotto.GeneralPaperTreeHistory

/-! Cumulative source profiles for the executed sparse history. Bounds also
cover every instruction prefix within a round. Generation of the selected
epoch's instruction lists and primitive bit/storage prices remain separate.
-/
namespace Blotto.GeneralPaperTreeHistoryWork
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperPreparedPowers
open GeneralPaperIntervalBatch GeneralPaperIntervalBatchBounds GeneralPaperTreeHistory
set_option autoImplicit false
set_option maxHeartbeats 3000000

def calls (batches : ℕ → List Instruction) : ℕ → ℕ
  | 0 => 0
  | t+1 => calls batches t+(batches t).length

theorem calls_monotone (batches : ℕ → List Instruction) : Monotone (calls batches) := by
  apply monotone_nat_of_le_succ
  intro t
  dsimp only [calls]
  omega

theorem node_bound (prepared : Prepared) (height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : 0<span) (t : ℕ) : nodes (execute prepared height span batches t).node≤1+4*height*calls batches t := by
  induction t with
  | zero => simp only [execute,nodes,calls,Nat.mul_zero,Nat.add_zero,le_refl]
  | succ t ih =>
    have hb := GeneralPaperIntervalBatchBounds.node_bound prepared height span (execute prepared height span batches t).node (batches t) hSpan
    dsimp only [execute,calls]
    nlinarith

theorem visit_bound (prepared : Prepared) (height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : 0<span) (t : ℕ) : (execute prepared height span batches t).visits≤(1+4*height)*calls batches t := by
  induction t with
  | zero => simp only [execute,calls,Nat.mul_zero,le_refl]
  | succ t ih =>
    have hb := GeneralPaperIntervalBatchBounds.visit_bound prepared height span (execute prepared height span batches t).node (batches t) hSpan
    dsimp only [execute,calls]
    nlinarith

theorem work_bound (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : 0<span) (t : ℕ) :
    (execute (prepare lambda k) height span batches t).work≤
      entryPrice (prepare lambda k) height*calls batches t+24*t+8 := by
  induction t with
  | zero => simp only [execute,calls,Nat.mul_zero,Nat.zero_add,le_refl]
  | succ t ih =>
    have hb := GeneralPaperIntervalBatchBounds.work_bound lambda k height span (execute (prepare lambda k) height span batches t).node (batches t) hSpan
    dsimp only [execute,calls]
    nlinarith

theorem within_round_nodes (prepared : Prepared) (height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : 0<span) (t n : ℕ) :
    nodes (GeneralPaperIntervalBatch.run prepared height span (execute prepared height span batches t).node ((batches t).take n)).node≤
      1+4*height*calls batches (t+1) := by
  have hp := prefix_nodes prepared height span (execute prepared height span batches t).node (batches t) hSpan n
  have ht := node_bound prepared height span batches hSpan t
  dsimp only [calls]
  nlinarith

theorem within_round_path (lambda k height : ℕ) (span : ℚ) (batches : ℕ → List Instruction)
    (hSpan : span=(2:ℚ)^height) (t n : ℕ)
    (hCount : t+1≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ r i, increments height batches r i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalBatch.run (prepare lambda k) height span
        (execute (prepare lambda k) height span batches t).node ((batches t).take n)).node := by
  intro i hi
  simp only [Nat.zero_add]
  rw [run_levels (prepare lambda k) height span _ ((batches t).take n) hSpan i hi,
    execute_levels (prepare lambda k) height span batches hSpan t ⟨i,hi⟩]
  have he := effect_take_le (batches t) n i
  have hc := GeneralPaperPowerPrecision.local_level_bound (Nat.two_pow_pos height) lambda k (t+1)
    (increments height batches) hCount hIncrement ⟨i,hi⟩
  change GeneralPaperGeometricLevels.levels (increments height batches) t ⟨i,hi⟩+effect (batches t) i≤_ at hc
  omega

end Blotto.GeneralPaperTreeHistoryWork
