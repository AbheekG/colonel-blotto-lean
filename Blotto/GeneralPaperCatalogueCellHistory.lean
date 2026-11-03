import Blotto.GeneralPaperCatalogueSnapshotScore

/-! Exact histories and epoch-end instructions of all four concrete cell
arrays. Reindexing preserves the native Array data and erases only plan-size
equalities. The instruction lists use the actual final arrays, not a fresh
loss simulation. Their full-code effects equal the executed local levels.
-/
namespace Blotto.GeneralPaperCatalogueCellHistory
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEpochDeltaSemantics GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

def partition {k : ℕ} (learner : Learner) (plan : GeneralPaperEpochFieldPlan.Plan k) : GeneralPaperPreparedPartition.Prepared :=
  match learner with
  | .p => plan.pCells.partition
  | .q => plan.qCells.partition
  | .lambda => plan.lambdaCells.partition
  | .mu => plan.muCells.partition

def cellArray {k : ℕ} (learner : Learner) (state : GeneralPaperEpochFieldState.State k) :
    FixedArrayTable (partition learner state.plan).count ℕ :=
  match learner with
  | .p => state.pCells
  | .q => state.qCells
  | .lambda => state.lambdaCells
  | .mu => state.muCells

def cellDelta {k : ℕ} {state : GeneralPaperEpochFieldState.State k} (learner : Learner) (delta : Deltas state) :
    FixedArrayTable (partition learner state.plan).count ℕ :=
  match learner with
  | .p => delta.pCells
  | .q => delta.qCells
  | .lambda => delta.lambdaCells
  | .mu => delta.muCells

def levelsOfState {m k : ℕ} {cache : Cache m k} (learner : Learner) (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m) :
    FixedArrayTable (partition learner (cache.plans.read j)).count ℕ :=
  GeneralPaperRowPrefix.resize (congrArg (fun plan => (partition learner plan).count) (state.plan_spec j))
    (cellArray learner (state.fields.read j))

def cellLevels {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m) :
    FixedArrayTable (partition learner (cache.plans.read j)).count ℕ := levelsOfState learner (stateAt run time) j

def delta {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m) :
    FixedArrayTable (partition learner (cache.plans.read j)).count ℕ :=
  GeneralPaperRowPrefix.resize (congrArg (fun plan => (partition learner plan).count) (field_plan run time j))
    (cellDelta learner (deltaAt run time j))

theorem table_data_eq {α : Type*} {n : ℕ} (x y : FixedArrayTable n α) (h : x.data=y.data) : x=y := by
  cases x
  cases y
  cases h
  rfl

theorem resize_advance {n p : ℕ} (h : n=p) (current changeBy : FixedArrayTable n ℕ) :
    GeneralPaperRowPrefix.resize h (GeneralPaperEpochLevelArray.advance current changeBy).1=
      (GeneralPaperEpochLevelArray.advance (GeneralPaperRowPrefix.resize h current) (GeneralPaperRowPrefix.resize h changeBy)).1 := by
  cases h
  rfl

theorem cell_step {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m) :
    cellLevels learner run (time+1) j=(GeneralPaperEpochLevelArray.advance (cellLevels learner run time j) (delta learner run time j)).1 := by
  apply table_data_eq
  change (cellArray learner (fieldAt run (time+1) j)).data=_
  rw [field_step]
  have he : cellArray learner (advance (fieldAt run time j) (deltaAt run time j))=
      (GeneralPaperEpochLevelArray.advance (cellArray learner (fieldAt run time j)) (cellDelta learner (deltaAt run time j))).1 := by
    cases learner <;> rfl
  rw [he]
  exact congrArg FixedArrayTable.data (resize_advance
    (congrArg (fun plan => (partition learner plan).count) (field_plan run time j))
    (cellArray learner (fieldAt run time j)) (cellDelta learner (deltaAt run time j)))

theorem cell_initial {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (j : Fin m) :
    cellLevels learner run 0 j=(GeneralPaperEpochLevelArray.initial (partition learner (cache.plans.read j)).count).1 := by
  apply table_data_eq
  change (cellArray learner (fieldAt run 0 j)).data=_
  rw [field_initial]
  cases learner <;> rfl

theorem cell_array {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    cellLevels learner run count j=(GeneralPaperEpochLevelArray.execute (fun t => delta learner run t j) count).1 := by
  induction count with
  | zero => exact cell_initial learner run j
  | succ t ih => rw [cell_step,ih]; rfl

def stateIncrement {k : ℕ} (learner : Learner) (state : GeneralPaperEpochFieldState.State k) (snapshot : Snapshot k)
    (choice : Choice state.plan) (code : ℕ) : ℕ :=
  match learner with
  | .p => pIncrement state snapshot code
  | .q => qIncrement state snapshot code
  | .lambda => lambdaIncrement state snapshot choice code
  | .mu => muIncrement state snapshot choice code

theorem transported_semantics {k : ℕ} (learner : Learner) (state : GeneralPaperEpochFieldState.State k) (snapshot : Snapshot k)
    (choice : Choice state.plan) (target : GeneralPaperEpochFieldPlan.Plan k) (hPlan : state.plan=target)
    (hOrdered : GeneralPaperEpochFieldPlan.Ordered state.plan) (hCodes : GeneralPaperEpochFieldPlan.CodesValid state.plan)
    (r : Fin (partition learner target).count) (code : ℕ) (hCell : Contains (partition learner target).intervals r code) :
    (GeneralPaperRowPrefix.resize (congrArg (fun plan => (partition learner plan).count) hPlan)
      (cellDelta learner (generate state snapshot choice).1)).read r=stateIncrement learner state snapshot choice code := by
  subst target
  cases learner with
  | p => exact p_cell state snapshot choice hOrdered hCodes r code hCell
  | q => exact q_cell state snapshot choice hOrdered hCodes r code hCell
  | lambda => exact lambda_cell state snapshot choice hOrdered hCodes r code hCell
  | mu => exact mu_cell state snapshot choice hOrdered hCodes r code hCell

theorem delta_semantics {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (time : ℕ) (j : Fin m)
    (r : Fin (partition learner (cache.plans.read j)).count) (code : ℕ)
    (hCell : Contains (partition learner (cache.plans.read j)).intervals r code) :
    (delta learner run time j).read r=increment learner run time j code := by
  have ho : GeneralPaperEpochFieldPlan.Ordered (fieldAt run time j).plan := by
    rw [field_plan]; exact field_ordered cache hOrdered j
  have hc : GeneralPaperEpochFieldPlan.CodesValid (fieldAt run time j).plan := by
    rw [field_plan]; exact field_codes cache hCodes j
  exact transported_semantics learner (fieldAt run time j) (snapshotAt run time j) (choiceAt run time j)
    (cache.plans.read j) (field_plan run time j) ho hc r code hCell

theorem partition_covers {m k : ℕ} (learner : Learner) (cache : Cache m k) (j : Fin m) :
    Covers (width learner cache) (partition learner (cache.plans.read j)).intervals := by
  cases learner <;> rw [GeneralPaperCatalogueEpochCache.plan_read]
  · exact GeneralPaperUnsignedPartition.covers _ _ _ _
  · exact GeneralPaperUnsignedPartition.covers _ _ _ _
  · exact GeneralPaperSignedPartition.covers _ _ _
  · exact GeneralPaperSignedPartition.covers _ _ _

theorem partition_disjoint {m k : ℕ} (learner : Learner) (cache : Cache m k) (j : Fin m) :
    GeneralPaperEpochCellInstructions.Disjoint (partition learner (cache.plans.read j)).intervals := by
  cases learner <;> rw [GeneralPaperCatalogueEpochCache.plan_read]
  · exact GeneralPaperUnsignedPartition.disjoint _ _ _ _
  · exact GeneralPaperUnsignedPartition.disjoint _ _ _ _
  · exact GeneralPaperSignedPartition.disjoint _ _ _
  · exact GeneralPaperSignedPartition.disjoint _ _ _

def batchOfState {m k : ℕ} {cache : Cache m k} (learner : Learner) (state : GeneralPaperCatalogueEpochCache.State cache) (j : Fin m) :
    List GeneralPaperIntervalBatch.Instruction :=
  GeneralPaperEpochCellInstructions.build (partition learner (cache.plans.read j)).intervals (levelsOfState learner state j)

def batch {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    List GeneralPaperIntervalBatch.Instruction := batchOfState learner (stateAt run count) j

theorem batch_effect {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (count : ℕ) (j : Fin m) (i : Fin (width learner cache)) :
    GeneralPaperIntervalBatch.effect (batch learner run count j) i.val=
      GeneralPaperGeometricLevels.levels (fun t (a : Fin (width learner cache)) => increment learner run t j a.val) count i := by
  change GeneralPaperIntervalBatch.effect
    (GeneralPaperEpochCellInstructions.build (partition learner (cache.plans.read j)).intervals (cellLevels learner run count j)) i.val=_
  rw [cell_array]
  have he := GeneralPaperEpochCellInstructions.cumulative_effect (partition learner (cache.plans.read j)).intervals
    (fun t => delta learner run t j) (fun t (a : Fin (width learner cache)) => increment learner run t j a.val) 0 count
    (partition_covers learner cache j) (partition_disjoint learner cache j)
    (fun t _ r a hCell => by simpa only [Nat.zero_add] using delta_semantics learner run hOrdered hCodes t j r a.val hCell) i
  simpa only [Nat.zero_add] using he

theorem cellArray_bound {k : ℕ} (learner : Learner) (state : GeneralPaperEpochFieldState.State k) (bound : ℕ)
    (hBound : Bounded state bound) (r : Fin (partition learner state.plan).count) : (cellArray learner state).read r≤bound := by
  cases learner with
  | p => exact hBound.2.2.2.2.1 r
  | q => exact hBound.2.2.2.2.2.1 r
  | lambda => exact hBound.2.2.2.2.2.2.1 r
  | mu => exact hBound.2.2.2.2.2.2.2 r

theorem cellLevels_bound {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m)
    (bound : ℕ) (hBound : Bounded (fieldAt run time j) bound) (r : Fin (partition learner (cache.plans.read j)).count) :
    (cellLevels learner run time j).read r≤bound := by
  let sourceIndex : Fin (partition learner (fieldAt run time j).plan).count :=
    ⟨r.val,by rw [field_plan]; exact r.isLt⟩
  exact cellArray_bound learner (fieldAt run time j) bound hBound sourceIndex

theorem batch_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (i : Fin (width learner cache)) :
    GeneralPaperIntervalBatch.effect (batch learner (selected cache Qv weights Bc Br) count j) i.val≤
      count*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator) := by
  obtain ⟨r,hr⟩ := partition_covers learner cache j i.val i.isLt
  change GeneralPaperIntervalBatch.effect
    (GeneralPaperEpochCellInstructions.build (partition learner (cache.plans.read j)).intervals
      (cellLevels learner (selected cache Qv weights Bc Br) count j)) i.val≤_
  rw [unique_effect _ _ (partition_disjoint learner cache j) r i.val hr]
  exact cellLevels_bound learner _ count j _ (selected_bounded cache Qv weights Bc Br count hCount j) r

end Blotto.GeneralPaperCatalogueCellHistory
