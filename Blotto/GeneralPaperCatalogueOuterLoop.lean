import Blotto.GeneralPaperCatalogueTrajectoryAppend

/-! The concrete four-tree outer loop. Each epoch constructs its own
summaries and catalogues from the current forest, executes both selectors,
retains that execution's candidate rows and updates that same forest using
the returned final arrays. Shared prepared data persist across epochs.
-/
namespace Blotto.GeneralPaperCatalogueOuterLoop
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
set_option autoImplicit false
set_option maxHeartbeats 3500000

def epoch {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) :
    Trees m a.lambda × Array (FixedArrayTable m ℕ) :=
  let c := cache shared a k trees
  let localResult := GeneralPaperCatalogueEpoch.execute c shared.powers shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br (GeneralPaperCatalogueEpochCache.initial c) shared.trajectory.period
  (GeneralPaperCatalogueForestUpdate.apply shared trees localResult.1,localResult.2)

theorem epoch_trees {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) :
    (epoch shared a k trees).1=GeneralPaperCatalogueForestUpdate.apply shared trees
      (GeneralPaperCatalogueEpochRun.stateAt (epochRun shared a k trees) shared.trajectory.period) := rfl

theorem epoch_size {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : Trees m a.lambda) :
    (epoch shared a k trees).2.size=shared.trajectory.period :=
  GeneralPaperCatalogueEpoch.trajectory_size _ _ _ _ _ _ _ _ _

def execute {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) : ℕ → Trees m a.lambda × Array (FixedArrayTable m ℕ)
  | 0 => (initial m a.lambda,#[])
  | count+1 =>
    let previous := execute shared a k count
    let next := epoch shared a k previous.1
    (next.1,GeneralPaperCatalogueTrajectoryAppend.append previous.2 next.2)

def treesAt {m : ℕ} (shared : Shared m) (a : Alphabet) (k count : ℕ) : Trees m a.lambda :=
  (execute shared a k count).1

def cacheAt {m : ℕ} (shared : Shared m) (a : Alphabet) (k count : ℕ) : GeneralPaperCatalogueEpochCache.Cache m k :=
  cache shared a k (treesAt shared a k count)

theorem trees_initial {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) : treesAt shared a k 0=initial m a.lambda := rfl

theorem trees_step {m : ℕ} (shared : Shared m) (a : Alphabet) (k count : ℕ) :
    treesAt shared a k (count+1)=(epoch shared a k (treesAt shared a k count)).1 := rfl

theorem trajectory_size {m : ℕ} (shared : Shared m) (a : Alphabet) (k count : ℕ) :
    (execute shared a k count).2.size=count*shared.trajectory.period := by
  induction count with
  | zero => simp only [execute,Array.size_empty,Nat.zero_mul]
  | succ count ih =>
    change (GeneralPaperCatalogueTrajectoryAppend.append (execute shared a k count).2
      (epoch shared a k (treesAt shared a k count)).2).size=_
    rw [GeneralPaperCatalogueTrajectoryAppend.size,ih,epoch_size]
    ring

theorem complete_size {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (execute (prepare a k Qv weights Bc Br) a k (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs).2.size=
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows := by
  rw [trajectory_size]
  rfl

end Blotto.GeneralPaperCatalogueOuterLoop
