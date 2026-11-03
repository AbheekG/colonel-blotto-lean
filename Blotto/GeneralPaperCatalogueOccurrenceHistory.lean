import Blotto.GeneralPaperCatalogueEpochRun

/-! Exact histories of all four occurrence arrays in the concrete native
epoch. A finite learner index selects existing stored arrays; all increment
functions below are derived from the execution's own snapshots and rows.
The selected-array observer refines the retained local power/prefix pipeline.
-/
namespace Blotto.GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas GeneralPaperEpochDeltaSemantics
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

inductive Learner where
  | p | q | lambda | mu
  deriving DecidableEq

def occurrence {k : ℕ} (learner : Learner) (state : GeneralPaperEpochFieldState.State k) : Summary k :=
  match learner with
  | .p => state.pOccurrences
  | .q => state.qOccurrences
  | .lambda => state.lambdaOccurrences
  | .mu => state.muOccurrences

def occurrenceDelta {k : ℕ} {state : GeneralPaperEpochFieldState.State k} (learner : Learner) (delta : Deltas state) : Summary k :=
  match learner with
  | .p => delta.pOccurrences
  | .q => delta.qOccurrences
  | .lambda => delta.lambdaOccurrences
  | .mu => delta.muOccurrences

def summary {m k : ℕ} (learner : Learner) (cache : Cache m k) (j : Fin m) : Summary k :=
  match learner with
  | .p => cache.p.read j
  | .q => cache.q.read j
  | .lambda => cache.lambda.read j
  | .mu => cache.mu.read j

def block {k : ℕ} (learner : Learner) (snapshot : Snapshot k) : Block k :=
  match learner with
  | .p => snapshot.p
  | .q => snapshot.q
  | .lambda => snapshot.lambda
  | .mu => snapshot.mu

def increment {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m) (code : ℕ) : ℕ :=
  match learner with
  | .p => pIncrement (fieldAt run time j) (snapshotAt run time j) code
  | .q => qIncrement (fieldAt run time j) (snapshotAt run time j) code
  | .lambda => lambdaIncrement (fieldAt run time j) (snapshotAt run time j) (choiceAt run time j) code
  | .mu => muIncrement (fieldAt run time j) (snapshotAt run time j) (choiceAt run time j) code

theorem delta_read {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (occurrenceDelta learner (deltaAt run time j)).read r=increment learner run time j ((summary learner cache j).read r) := by
  cases learner <;> dsimp only [occurrenceDelta,deltaAt,increment,summary]
  · rw [p_occurrence,field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl
  · rw [q_occurrence,field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl
  · rw [lambda_occurrence,field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl
  · rw [mu_occurrence,field_plan,GeneralPaperCatalogueEpochCache.plan_read]
    rfl

theorem occurrence_advance {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (time : ℕ) (j : Fin m) :
    occurrence learner (fieldAt run (time+1) j)=
      (GeneralPaperEpochLevelArray.advance (occurrence learner (fieldAt run time j)) (occurrenceDelta learner (deltaAt run time j))).1 := by
  rw [field_step]
  cases learner <;> rfl

theorem occurrence_initial {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (j : Fin m) :
    occurrence learner (fieldAt run 0 j)=(GeneralPaperEpochLevelArray.initial (GeneralPaperSourceParameters.prepare k).summarySize).1 := by
  cases learner <;> simp only [occurrence,fieldAt,stateAt,GeneralPaperCatalogueEpoch.execute,
    GeneralPaperCatalogueEpochCache.initial,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,GeneralPaperEpochFieldState.initial]

theorem occurrence_array {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    occurrence learner (fieldAt run count j)=
      (GeneralPaperEpochLevelArray.execute (fun t => occurrenceDelta learner (deltaAt run t j)) count).1 := by
  induction count with
  | zero => exact occurrence_initial learner run j
  | succ t ih =>
    rw [occurrence_advance,ih]
    rfl

theorem occurrence_levels {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (occurrence learner (fieldAt run count j)).read r=
      GeneralPaperGeometricLevels.levels (fun t a => increment learner run t j ((summary learner cache j).read a)) count r := by
  rw [occurrence_array,GeneralPaperEpochLevelArray.execute_read]
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t _
  exact delta_read learner run t j r

theorem snapshot_block {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    block learner (snapshotAt run count j)=GeneralPaperEpochSnapshot.block run.powers (occurrence learner (fieldAt run count j)) := by
  rw [snapshot_take]
  cases learner <;> rfl

theorem block_prefix {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    (block learner (snapshotAt run count j)).cdf=
      GeneralPaperEpochCachedQuery.prefixes run.powers (fun t => occurrenceDelta learner (deltaAt run t j)) count := by
  rw [snapshot_block,occurrence_array]
  rfl

theorem block_numerators {m k : ℕ} {cache : Cache m k} (learner : Learner) (run : Run cache) (count : ℕ) (j : Fin m) :
    (block learner (snapshotAt run count j)).values=
      GeneralPaperEpochCachedQuery.numerators run.powers (fun t => occurrenceDelta learner (deltaAt run t j)) count := by
  rw [snapshot_block,occurrence_array]
  rfl

end Blotto.GeneralPaperCatalogueOccurrenceHistory
