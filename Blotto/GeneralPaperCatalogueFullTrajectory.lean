import Blotto.GeneralPaperCatalogueGlobalErrors

/-! The complete T-row code table reuses the already-produced output
array. Its sized wrapper erases only the length proof; no table replay or
coordinate recombination is needed. Every row has its native whole-row
decode and canonical hard-budget certificate.
-/
namespace Blotto.GeneralPaperCatalogueFullTrajectory
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 3500000

def table {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    FixedArrayTable (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (FixedArrayTable m ℕ) :=
  ⟨(execute (prepare a k Qv weights Bc Br) a k (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).2,
    complete_size a k Qv weights Bc Br⟩

theorem time_partition (period time : ℕ) : (time/period)*period+time%period=time := by
  have h := Nat.mod_add_div time period
  simpa only [Nat.mul_comm,Nat.add_comm] using h

theorem read_preupdate {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    (table a k Qv weights Bc Br).read time=
      GeneralPaperCatalogueTrueScore.chosenCodes false
        (epochRun (prepare a k Qv weights Bc Br) a k
          (treesAt (prepare a k Qv weights Bc Br) a k (time.val/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)))
        (time.val%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) := by
  have ht := Nat.mod_lt time.val (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k)
  have he := GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time.val time.isLt
  have hread := GeneralPaperCatalogueOuterTrajectory.global_preupdate (prepare a k Qv weights Bc Br) a k
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs (time.val/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (time.val%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) he ht
  simpa only [prepared_period,time_partition,table,FixedArrayTable.read] using hread

theorem every_row_feasible {m : ℕ} (a : Alphabet) (k Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hB : 0≤Bc) (hBudgetDen : Bc.den∣q)
    (time : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    ∃ choices : FixedArrayTable m Choice,
      (∀ j, (GeneralPaperCodeDecode.decode a false (((table a k Qv weights Bc Br).read time).read j)).choice=some (choices.read j)) ∧
      Feasible (Bc:ℝ) (fun j => ((choices.read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)) := by
  have ht := Nat.mod_lt time.val (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k)
  have he := GeneralPaperCatalogueGlobalErrors.epoch_index_lt a.lambda k time.val time.isLt
  have hr := GeneralPaperCatalogueOuterTrajectory.recorded_candidate_feasible a k Qv q qbar hm hQv hq hCap weights hWeights Bc Br hB hBudgetDen
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs (time.val/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (time.val%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) he ht
  simpa only [prepared_period,time_partition,table,FixedArrayTable.read] using hr

end Blotto.GeneralPaperCatalogueFullTrajectory
