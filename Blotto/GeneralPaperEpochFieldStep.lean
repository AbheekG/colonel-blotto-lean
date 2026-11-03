import Blotto.GeneralPaperEpochDeltas

/-! One simultaneous four-block step. Positive snapshot totals and bounded
increments are consequences of the current exact level cap. No positivity
oracle, independence of adaptive updates or already-proved loss history is
required for this induction.
-/
namespace Blotto.GeneralPaperEpochFieldStep
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
set_option autoImplicit false
set_option maxHeartbeats 3500000

def step {k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (state : State k) (choice : Choice state.plan) : State k :=
  advance state (generate state (take prepared state) choice).1

theorem step_plan {k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (state : State k) (choice : Choice state.plan) :
    (step prepared state choice).plan=state.plan := rfl

theorem epoch_cap (lambda k time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) :
    time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)≤GeneralPaperPowerPrecision.levelBound lambda k := by
  have ht := hTime.trans (GeneralPaperEpochPowerQueries.period_le_rows lambda k)
  calc
    _ ≤ (GeneralPaperTrajectoryParameters.prepare lambda k).rows*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :=
      Nat.mul_le_mul_right _ ht
    _ = _ := by unfold GeneralPaperPowerPrecision.levelBound; ring

theorem snapshot_positive (lambda k : ℕ) (state : State k) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hState : Bounded state (time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator))) :
    Positive (take (GeneralPaperPreparedPowers.prepare lambda k) state) :=
  take_positive lambda k state (bounded_mono state _ _ hState (epoch_cap lambda k time hTime))

theorem step_bounded (lambda k : ℕ) (state : State k) (choice : Choice state.plan) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hState : Bounded state (time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator))) :
    Bounded (step (GeneralPaperPreparedPowers.prepare lambda k) state choice)
      ((time+1)*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) := by
  have hp := snapshot_positive lambda k state time hTime hState
  have hd := generated_bound state _ choice hp (take_coherent _ state)
  simpa only [step,Nat.add_mul,Nat.one_mul] using advance_bounded state _ _ _ hState hd

end Blotto.GeneralPaperEpochFieldStep
