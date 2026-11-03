import Blotto.GeneralPaperTrajectoryAppendPrice

/-! The full trajectory source retains shared preparation, advances one
forest per epoch, and appends only the returned new rows. Its two control
capacities are the retained epoch count and total trajectory length. -/
namespace Blotto.GeneralPaperGeometricSourceExecution
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOuterLoop
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def step {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) (previous : Trees m a.lambda × Array (FixedArrayTable m ℕ)) :
    (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × ℕ :=
  let next := GeneralPaperOuterEpochExecution.run bits index model W k Qv a c hc shared previous.1
  let appended := GeneralPaperTrajectoryAppendExecution.run bits index W shared.trajectory.rows previous.2 next.1.2
  let A := if bits then arrayWord W (shared.trajectory.epochs+2) else W
  ((next.1.1,appended.1),next.2+appended.2+GeneralPaperLocalEpochExecution.control index A (count+1))

def run {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) : ℕ → (Trees m a.lambda × Array (FixedArrayTable m ℕ)) × ℕ :=
  Nat.rec (by exact
    let forest := GeneralPaperForestInitialPrice.run bits index W m a.lambda
    let A := if bits then arrayWord W (shared.trajectory.rows+2) else W
    ((forest.1,#[]),forest.2+PaperIndexedArrayConstruction.initialWork index A shared.trajectory.rows+
      GeneralPaperIntegerWordPrice.compare index 0 0+64*A)) (fun count previous =>
    let next := step bits index model W k Qv a c hc shared count previous.1
    (next.1,previous.2+next.2))

theorem run_succ {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) :
    run bits index model W k Qv a c hc shared (count+1)=
      let previous := run bits index model W k Qv a c hc shared count
      let next := step bits index model W k Qv a c hc shared count previous.1
      (next.1,previous.2+next.2) := rfl

theorem step_data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (step bits index model W k Qv a c hc shared count (GeneralPaperCatalogueOuterLoop.execute shared a k count)).1=
      GeneralPaperCatalogueOuterLoop.execute shared a k (count+1) := by
  dsimp only
  unfold step
  dsimp only
  erw [GeneralPaperOuterEpochExecution.data bits index model W k Qv a c hc weights Bc Br count he,
    GeneralPaperTrajectoryAppendExecution.data]
  rfl

theorem data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (run bits index model W k Qv a c hc shared count).1=GeneralPaperCatalogueOuterLoop.execute shared a k count := by
  induction count with
  | zero => exact congrArg (fun t => (t,#[])) (GeneralPaperForestInitialPrice.data bits index W m a.lambda)
  | succ count ih =>
    dsimp only
    rw [run_succ]
    dsimp only
    rw [ih (by omega)]
    exact step_data bits index model W k Qv a c hc weights Bc Br count he

theorem size {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    (run bits index model W k Qv a c hc shared count).1.2.size=count*shared.trajectory.period := by
  dsimp only
  rw [data bits index model W k Qv a c hc weights Bc Br count he,GeneralPaperCatalogueOuterLoop.trajectory_size]

end Blotto.GeneralPaperGeometricSourceExecution
