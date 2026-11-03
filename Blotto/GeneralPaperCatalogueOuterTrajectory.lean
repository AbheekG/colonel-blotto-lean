import Blotto.GeneralPaperCatalogueGlobalHistory

/-! Every global output row is exactly one pre-update candidate of the
same own-tree execution. Appending an epoch preserves every earlier row.
No epoch subsampling, marginal recombination or extra optimizer call is
used to define the returned full trajectory.
-/
namespace Blotto.GeneralPaperCatalogueOuterTrajectory
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem row_index_lt (period count epoch time : ℕ) (he : epoch<count) (ht : time<period) :
    epoch*period+time<count*period := by
  have hc := Nat.mul_le_mul_right period (show epoch+1≤count by omega)
  nlinarith only [ht,hc]

theorem trajectory_read {m : ℕ} (shared : Shared m) (a : Alphabet) (k count epochIndex time : ℕ)
    (he : epochIndex<count) (ht : time<shared.trajectory.period) :
    (execute shared a k count).2[epochIndex*shared.trajectory.period+time]'(by rw [trajectory_size]; exact row_index_lt _ _ _ _ he ht)=
      (epoch shared a k (treesAt shared a k epochIndex)).2[time]'(by rw [epoch_size]; exact ht) := by
  induction count with
  | zero => omega
  | succ count ih =>
    change (GeneralPaperCatalogueTrajectoryAppend.append (execute shared a k count).2
      (epoch shared a k (treesAt shared a k count)).2)[epochIndex*shared.trajectory.period+time]'(by
        rw [GeneralPaperCatalogueTrajectoryAppend.size,trajectory_size,epoch_size]
        have h := row_index_lt _ _ _ _ he ht
        simpa only [Nat.succ_mul] using h)=
      (epoch shared a k (treesAt shared a k epochIndex)).2[time]'(by rw [epoch_size]; exact ht)
    by_cases hc : epochIndex<count
    · exact (GeneralPaperCatalogueTrajectoryAppend.old (execute shared a k count).2
        (epoch shared a k (treesAt shared a k count)).2 _
        (by rw [trajectory_size]; exact row_index_lt _ _ _ _ hc ht)).trans (ih hc)
    · have heq : epochIndex=count := by omega
      subst epochIndex
      have hr := GeneralPaperCatalogueTrajectoryAppend.new (execute shared a k count).2
        (epoch shared a k (treesAt shared a k count)).2 time (by rw [epoch_size]; exact ht)
      simpa only [trajectory_size] using hr

theorem epoch_preupdate {m : ℕ} (shared : Shared m) (a : Alphabet) (k epochIndex time : ℕ)
    (ht : time<shared.trajectory.period) :
    (epoch shared a k (treesAt shared a k epochIndex)).2[time]'(by rw [epoch_size]; exact ht)=
      (GeneralPaperCatalogueEpoch.round (cacheAt shared a k epochIndex) shared.powers shared.profit shared.trajectory.rows
        shared.weights shared.Bc shared.Br
        (GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k (treesAt shared a k epochIndex)) time)).candidate :=
  GeneralPaperCatalogueEpoch.trajectory_read _ _ _ _ _ _ _ _ _ _ ht

theorem global_preupdate {m : ℕ} (shared : Shared m) (a : Alphabet) (k count epochIndex time : ℕ)
    (he : epochIndex<count) (ht : time<shared.trajectory.period) :
    (execute shared a k count).2[epochIndex*shared.trajectory.period+time]'(by rw [trajectory_size]; exact row_index_lt _ _ _ _ he ht)=
      GeneralPaperCatalogueTrueScore.chosenCodes false (epochRun shared a k (treesAt shared a k epochIndex)) time := by
  rw [trajectory_read shared a k count epochIndex time he ht,epoch_preupdate shared a k epochIndex time ht]
  rfl

theorem recorded_candidate_feasible {m : ℕ} (a : Alphabet) (k Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hB : 0≤Bc) (hBudgetDen : Bc.den∣q) (count epochIndex time : ℕ)
    (he : epochIndex<count) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := prepare a k Qv weights Bc Br
    ∃ choices : FixedArrayTable m GeneralPaperCodeAlphabet.Choice,
      (∀ j, (GeneralPaperCodeDecode.decode a false
        (((execute shared a k count).2[epochIndex*shared.trajectory.period+time]'(by rw [trajectory_size]; exact row_index_lt _ _ _ _ he ht)).read j)).choice=
          some (choices.read j)) ∧
      Feasible (Bc:ℝ) (fun j => ((choices.read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar a.C):ℝ)) := by
  dsimp only
  let shared := prepare a k Qv weights Bc Br
  let c := cacheAt shared a k epochIndex
  have hr := GeneralPaperCatalogueEpochOutput.recorded_candidate_feasible c Qv q qbar hm hQv hq hCap weights hWeights Bc Br hB hBudgetDen
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period time le_rfl ht
  obtain ⟨choices,hd,hf⟩ := hr
  refine ⟨choices,?_,hf⟩
  intro j
  rw [trajectory_read shared a k count epochIndex time he ht]
  exact hd j

end Blotto.GeneralPaperCatalogueOuterTrajectory
