import Blotto.GeneralPaperEpochDeltaSemantics

/-! Exact occurrence histories of the executed adaptive four-family loop.
The next prefix arrays are computed from the same accumulated levels proved
here; the per-round increment functions may depend on every prior state.
-/
namespace Blotto.GeneralPaperAdaptiveEpochHistory
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperAdaptiveEpoch GeneralPaperEpochDeltaSemantics GeneralPaperGeometricLevels
set_option autoImplicit false
set_option maxHeartbeats 3500000

def fieldAt {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) : State k := (execute prepared select first time).1.read j

def snapshotAt {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) : Snapshot k := take prepared (fieldAt prepared select first time j)

def choiceAt {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) : Choice (fieldAt prepared select first time j).plan :=
  (select (execute prepared select first time).1 (snapshots prepared (execute prepared select first time).1)).choice j

theorem field_step {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) :
    fieldAt prepared select first (time+1) j=GeneralPaperEpochFieldStep.step prepared (fieldAt prepared select first time j)
      (choiceAt prepared select first time j) := by
  unfold fieldAt
  rw [execute_step,round_field]
  rfl

theorem p_read_succ {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select first (time+1) j).pOccurrences.read r=
      (fieldAt prepared select first time j).pOccurrences.read r+
        pIncrement (fieldAt prepared select first time j) (snapshotAt prepared select first time j)
          ((fieldAt prepared select first time j).plan.pSummary.read r) := by
  rw [field_step]
  change (GeneralPaperEpochLevelArray.advance _ _).1.read r=_
  rw [GeneralPaperEpochLevelArray.advance_read,p_occurrence]
  rfl

theorem q_read_succ {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select first (time+1) j).qOccurrences.read r=
      (fieldAt prepared select first time j).qOccurrences.read r+
        qIncrement (fieldAt prepared select first time j) (snapshotAt prepared select first time j)
          ((fieldAt prepared select first time j).plan.qSummary.read r) := by
  rw [field_step]
  change (GeneralPaperEpochLevelArray.advance _ _).1.read r=_
  rw [GeneralPaperEpochLevelArray.advance_read,q_occurrence]
  rfl

theorem lambda_read_succ {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select first (time+1) j).lambdaOccurrences.read r=
      (fieldAt prepared select first time j).lambdaOccurrences.read r+
        lambdaIncrement (fieldAt prepared select first time j) (snapshotAt prepared select first time j)
          (choiceAt prepared select first time j) ((fieldAt prepared select first time j).plan.lambdaSummary.read r) := by
  rw [field_step]
  change (GeneralPaperEpochLevelArray.advance _ _).1.read r=_
  rw [GeneralPaperEpochLevelArray.advance_read,lambda_occurrence]
  rfl

theorem mu_read_succ {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (first : Fields n k) (time : ℕ) (j : Fin n) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select first (time+1) j).muOccurrences.read r=
      (fieldAt prepared select first time j).muOccurrences.read r+
        muIncrement (fieldAt prepared select first time j) (snapshotAt prepared select first time j)
          (choiceAt prepared select first time j) ((fieldAt prepared select first time j).plan.muSummary.read r) := by
  rw [field_step]
  change (GeneralPaperEpochLevelArray.advance _ _).1.read r=_
  rw [GeneralPaperEpochLevelArray.advance_read,mu_occurrence]
  rfl

theorem p_levels {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (count : ℕ) (j : Fin n)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select (initial plans) count j).pOccurrences.read r=
      levels (fun t a => pIncrement (fieldAt prepared select (initial plans) t j) (snapshotAt prepared select (initial plans) t j)
        ((plans.read j).pSummary.read a)) count r := by
  induction count with
  | zero => simp only [fieldAt,execute,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,GeneralPaperEpochFieldState.initial,
      GeneralPaperEpochLevelArray.initialize_read,levels]
  | succ t ih =>
    rw [p_read_succ,ih]
    change _+pIncrement _ _ ((fieldAt prepared select (initial plans) t j).plan.pSummary.read r)=_+pIncrement _ _ ((plans.read j).pSummary.read r)
    rw [show (fieldAt prepared select (initial plans) t j).plan=plans.read j from
      GeneralPaperAdaptiveEpochBounds.initial_plan prepared select plans t j]

theorem q_levels {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (count : ℕ) (j : Fin n)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select (initial plans) count j).qOccurrences.read r=
      levels (fun t a => qIncrement (fieldAt prepared select (initial plans) t j) (snapshotAt prepared select (initial plans) t j)
        ((plans.read j).qSummary.read a)) count r := by
  induction count with
  | zero => simp only [fieldAt,execute,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,GeneralPaperEpochFieldState.initial,
      GeneralPaperEpochLevelArray.initialize_read,levels]
  | succ t ih =>
    rw [q_read_succ,ih]
    change _+qIncrement _ _ ((fieldAt prepared select (initial plans) t j).plan.qSummary.read r)=_+qIncrement _ _ ((plans.read j).qSummary.read r)
    rw [show (fieldAt prepared select (initial plans) t j).plan=plans.read j from
      GeneralPaperAdaptiveEpochBounds.initial_plan prepared select plans t j]

theorem lambda_levels {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (count : ℕ) (j : Fin n)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select (initial plans) count j).lambdaOccurrences.read r=
      levels (fun t a => lambdaIncrement (fieldAt prepared select (initial plans) t j) (snapshotAt prepared select (initial plans) t j)
        (choiceAt prepared select (initial plans) t j) ((plans.read j).lambdaSummary.read a)) count r := by
  induction count with
  | zero => simp only [fieldAt,execute,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,GeneralPaperEpochFieldState.initial,
      GeneralPaperEpochLevelArray.initialize_read,levels]
  | succ t ih =>
    rw [lambda_read_succ,ih]
    change _+lambdaIncrement _ _ _ ((fieldAt prepared select (initial plans) t j).plan.lambdaSummary.read r)=_+lambdaIncrement _ _ _ ((plans.read j).lambdaSummary.read r)
    rw [show (fieldAt prepared select (initial plans) t j).plan=plans.read j from
      GeneralPaperAdaptiveEpochBounds.initial_plan prepared select plans t j]

theorem mu_levels {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k)
    (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) (count : ℕ) (j : Fin n)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (fieldAt prepared select (initial plans) count j).muOccurrences.read r=
      levels (fun t a => muIncrement (fieldAt prepared select (initial plans) t j) (snapshotAt prepared select (initial plans) t j)
        (choiceAt prepared select (initial plans) t j) ((plans.read j).muSummary.read a)) count r := by
  induction count with
  | zero => simp only [fieldAt,execute,GeneralPaperAdaptiveEpoch.initial,FixedArrayTable.read_ofFn,GeneralPaperEpochFieldState.initial,
      GeneralPaperEpochLevelArray.initialize_read,levels]
  | succ t ih =>
    rw [mu_read_succ,ih]
    change _+muIncrement _ _ _ ((fieldAt prepared select (initial plans) t j).plan.muSummary.read r)=_+muIncrement _ _ _ ((plans.read j).muSummary.read r)
    rw [show (fieldAt prepared select (initial plans) t j).plan=plans.read j from
      GeneralPaperAdaptiveEpochBounds.initial_plan prepared select plans t j]

end Blotto.GeneralPaperAdaptiveEpochHistory
