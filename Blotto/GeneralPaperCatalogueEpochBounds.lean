import Blotto.GeneralPaperCatalogueEpoch

/-! Exact level caps and positive coherent snapshots of the actual native
catalogue epoch. The induction uses the executed two row optimizers and all
eight generated arrays. No selector parameter or positivity oracle remains.
-/
namespace Blotto.GeneralPaperCatalogueEpochBounds
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpoch
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem execute_plan {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (first : GeneralPaperCatalogueEpochCache.State cache) (time : ℕ) (j : Fin m) :
    (((execute cache powers profit T weights Bc Br first time).1.fields.read j).plan)=cache.plans.read j :=
  (execute cache powers profit T weights Bc Br first time).1.plan_spec j

theorem execute_bounded {m k : ℕ} (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    Bounded ((execute cache (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k) profit T weights Bc Br (initial cache) time).1.fields.read j)
      (time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) := by
  revert hTime j
  induction time with
  | zero =>
    intro _ j
    simpa only [execute,GeneralPaperCatalogueEpochCache.initial,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,Nat.zero_mul]
      using initial_bounded (cache.plans.read j)
  | succ t ih =>
    intro hTime j
    rw [execute_step,round_field]
    apply GeneralPaperEpochFieldStep.step_bounded cache.alphabet.lambda k _ _ t (by omega)
    exact ih (by omega) j

theorem execute_cap {m k : ℕ} (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    Bounded ((execute cache (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k) profit T weights Bc Br (initial cache) time).1.fields.read j)
      (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :=
  bounded_mono _ _ _ (execute_bounded cache profit T weights Bc Br time hTime j)
    (GeneralPaperEpochFieldStep.epoch_cap cache.alphabet.lambda k time hTime)

theorem snapshots_positive {m k : ℕ} (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    Positive ((GeneralPaperAdaptiveEpoch.snapshots (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k)
      (execute cache (GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k) profit T weights Bc Br (initial cache) time).1.fields).read j) := by
  rw [GeneralPaperAdaptiveEpoch.snapshots,FixedArrayTable.read_ofFn]
  exact take_positive cache.alphabet.lambda k _ (execute_cap cache profit T weights Bc Br time hTime j)

theorem snapshots_coherent {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m) :
    Coherent ((GeneralPaperAdaptiveEpoch.snapshots powers state.fields).read j) := by
  rw [GeneralPaperAdaptiveEpoch.snapshots,FixedArrayTable.read_ofFn]
  exact take_coherent powers _

end Blotto.GeneralPaperCatalogueEpochBounds
