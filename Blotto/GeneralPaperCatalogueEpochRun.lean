import Blotto.GeneralPaperCatalogueEpochOutput

/-! One retained execution setup for the concrete catalogue epoch. Selected
powers, profit grid and total trajectory length are constructed once and
passed unchanged to every round. The time-indexed views below are analysis
observers of that execution, not extra source calls or update callbacks.
-/
namespace Blotto.GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows GeneralPaperCatalogueEpoch
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

structure Run {m k : ℕ} (cache : Cache m k) where
  powers : GeneralPaperPreparedPowers.Prepared
  profit : GeneralPaperProfitParameters.Prepared
  T : ℕ
  weights : FixedArrayTable m ℕ
  Bc : ℚ
  Br : ℚ

def selected {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : Run cache :=
  ⟨GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k,
    GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv,
    (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows,weights,Bc,Br⟩

def stateAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) : GeneralPaperCatalogueEpochCache.State cache :=
  (execute cache run.powers run.profit run.T run.weights run.Bc run.Br (initial cache) time).1

def beforeAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) : FixedArrayTable m (Snapshot k) :=
  GeneralPaperAdaptiveEpoch.snapshots run.powers (stateAt run time).fields

def rowsAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) : Rows m k :=
  chooseRows cache run.profit run.T run.weights (beforeAt run time) run.Bc run.Br

def fieldAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) : GeneralPaperEpochFieldState.State k :=
  (stateAt run time).fields.read j

def snapshotAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) : Snapshot k :=
  (beforeAt run time).read j

def choiceAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) : Choice (fieldAt run time j).plan :=
  (rowsAt run time).fieldChoice (stateAt run time) j

def deltaAt {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) : Deltas (fieldAt run time j) :=
  (generate (fieldAt run time j) (snapshotAt run time j) (choiceAt run time j)).1

theorem field_plan {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) :
    (fieldAt run time j).plan=cache.plans.read j := (stateAt run time).plan_spec j

theorem field_initial {m k : ℕ} {cache : Cache m k} (run : Run cache) (j : Fin m) :
    fieldAt run 0 j=GeneralPaperEpochFieldState.initial (cache.plans.read j) := by
  change (FixedArrayTable.ofFn (fun i => GeneralPaperEpochFieldState.initial (cache.plans.read i))).read j=_
  exact FixedArrayTable.read_ofFn _ j

theorem snapshot_take {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) :
    snapshotAt run time j=take run.powers (fieldAt run time j) := by
  rw [snapshotAt,beforeAt,GeneralPaperAdaptiveEpoch.snapshots,FixedArrayTable.read_ofFn]
  rfl

theorem field_step {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) :
    fieldAt run (time+1) j=advance (fieldAt run time j) (deltaAt run time j) := by
  change (FixedArrayTable.ofFn (fun i : Fin m => advance (fieldAt run time i) (deltaAt run time i))).read j=_
  exact FixedArrayTable.read_ofFn _ j

theorem snapshot_coherent {m k : ℕ} {cache : Cache m k} (run : Run cache) (time : ℕ) (j : Fin m) :
    Coherent (snapshotAt run time j) := by
  rw [snapshot_take]
  exact take_coherent _ _

theorem selected_cap {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    Bounded (fieldAt (selected cache Qv weights Bc Br) time j) (GeneralPaperPowerPrecision.levelBound cache.alphabet.lambda k) :=
  GeneralPaperCatalogueEpochBounds.execute_cap cache _ _ weights Bc Br time hTime j

theorem selected_bounded {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    Bounded (fieldAt (selected cache Qv weights Bc Br) time j)
      (time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) :=
  GeneralPaperCatalogueEpochBounds.execute_bounded cache _ _ weights Bc Br time hTime j

theorem selected_positive {m k : ℕ} (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    Positive (snapshotAt (selected cache Qv weights Bc Br) time j) :=
  GeneralPaperCatalogueEpochBounds.snapshots_positive cache _ _ weights Bc Br time hTime j

end Blotto.GeneralPaperCatalogueEpochRun
