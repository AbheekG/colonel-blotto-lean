import Blotto.GeneralPaperPreparedSharedSource

/-! Pass the returned alphabet and Shared record into the selected full
pre-update trajectory. Execution consumes the preparation once. These are
exact source-data handoff theorems; full source execution prices remain a
separate join through its cached summaries/tree/optimizer operations.
-/
namespace Blotto.GeneralPaperPreparedSharedExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev Ready (m : ℕ) :=
  (((GeneralPaperPrecallCachePrice.Cache × GeneralPaperCodeAlphabet.Alphabet) × GeneralPaperProxyClassifier.Result) ×
    GeneralPaperCatalogueShared.Shared m) × GeneralPaperMaterializedGridCache.Cache

def codes {m : ℕ} (k : ℕ) (ready : Ready m) : Array (FixedArrayTable m ℕ) :=
  let a := ready.1.1.1.2
  let shared := ready.1.2
  (GeneralPaperCatalogueOuterLoop.execute shared a k shared.trajectory.epochs).2

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    codes k (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1=
      (GeneralPaperCatalogueFullTrajectory.table (GeneralPaperProxyParameters.alphabet m k) k Qv weights Bc Br).data := by
  rw [GeneralPaperPreparedSharedSource.data]
  rfl

theorem arithmetic_data {m : ℕ} (k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    codes k (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1=
      (GeneralPaperCatalogueFullTrajectory.table (GeneralPaperProxyParameters.alphabet m k) k Qv weights Bc Br).data := by
  rw [GeneralPaperPreparedSharedSource.arithmetic_data]
  rfl

theorem same_data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    codes k (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1=
      codes k (GeneralPaperPreparedSharedSource.arithmetic k Qv (b:ℝ) weights Bc Br).1 := by
  rw [data,arithmetic_data]

theorem size {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (codes k (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1).size=
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows := by
  rw [data]
  exact (GeneralPaperCatalogueFullTrajectory.table _ _ _ _ _ _).size

theorem arithmetic_size {m : ℕ} (k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (codes k (GeneralPaperPreparedSharedSource.arithmetic k Qv b weights Bc Br).1).size=
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows := by
  rw [arithmetic_data]
  exact (GeneralPaperCatalogueFullTrajectory.table _ _ _ _ _ _).size

end Blotto.GeneralPaperPreparedSharedExecution
