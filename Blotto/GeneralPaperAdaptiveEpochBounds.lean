import Blotto.GeneralPaperAdaptiveEpoch

/-! The actual adaptive run preserves every plan and bounds all cell and
occurrence levels at every round. Its own stored powers therefore supply
positive prefix totals. No assumptions on selector optimality are used here;
the separate optimizer/security join remains necessary.
-/
namespace Blotto.GeneralPaperAdaptiveEpochBounds
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperAdaptiveEpoch
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem execute_plan {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) :
    ((execute prepared select first time).1.read j).plan=(first.read j).plan := by
  induction time with
  | zero => rfl
  | succ t ih => rw [execute_step,round_plan,ih]

theorem initial_plan {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (time : ℕ) (j : Fin n) :
    ((execute prepared select (initial plans) time).1.read j).plan=plans.read j := by
  rw [execute_plan,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn]
  rfl

theorem execute_bounded {n : ℕ} (lambda k : ℕ) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) (j : Fin n) :
    Bounded ((execute (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time).1.read j)
      (time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) := by
  revert hTime j
  induction time with
  | zero =>
    intro _ j
    simpa only [execute,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,Nat.zero_mul] using initial_bounded (plans.read j)
  | succ t ih =>
    intro hTime j
    rw [execute_step,round_field]
    apply GeneralPaperEpochFieldStep.step_bounded lambda k _ _ t (by omega)
    exact ih (by omega) j

theorem execute_cap {n : ℕ} (lambda k : ℕ) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) (j : Fin n) :
    Bounded ((execute (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time).1.read j)
      (GeneralPaperPowerPrecision.levelBound lambda k) :=
  bounded_mono _ _ _ (execute_bounded lambda k select plans time hTime j) (GeneralPaperEpochFieldStep.epoch_cap lambda k time hTime)

theorem snapshots_positive {n : ℕ} (lambda k : ℕ) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) (j : Fin n) :
    Positive ((snapshots (GeneralPaperPreparedPowers.prepare lambda k)
      (execute (GeneralPaperPreparedPowers.prepare lambda k) select (initial plans) time).1).read j) := by
  rw [snapshots,FixedArrayTable.read_ofFn]
  exact take_positive lambda k _ (execute_cap lambda k select plans time hTime j)

theorem snapshots_coherent {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) :
    Coherent ((snapshots prepared (execute prepared select first time).1).read j) := by
  rw [snapshots,FixedArrayTable.read_ofFn]
  exact take_coherent _ _

theorem trajectory_read {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (count time : ℕ) (hTime : time<count) :
    (execute prepared select first count).2[time]'(by rw [trajectory_size]; exact hTime)=
      (round prepared select (execute prepared select first time).1).candidate := by
  induction count with
  | zero => omega
  | succ count ih =>
    change ((execute prepared select first count).2.push
      (round prepared select (execute prepared select first count).1).candidate)[time]'(by
        rw [Array.size_push,trajectory_size]; exact hTime)=_
    rw [Array.getElem_push]
    split_ifs with h
    · exact ih (by rw [trajectory_size] at h; exact h)
    · have he : time=count := by rw [trajectory_size] at h; omega
      subst time
      rfl

end Blotto.GeneralPaperAdaptiveEpochBounds
