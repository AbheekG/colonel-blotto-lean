import Blotto.GeneralPaperEpochFieldStep

/-! Native all-battlefield adaptive epoch execution. One deterministic row
selector sees all four pre-update snapshots of every battlefield and returns
one pair of complete option-index rows. The same snapshot and rows feed all
eight updates. The actual profit optimizer must still instantiate selector.
Only complete candidate rows are retained in the output trajectory.
-/
namespace Blotto.GeneralPaperAdaptiveEpoch
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
set_option autoImplicit false
set_option maxHeartbeats 3500000

abbrev Fields (n k : ℕ) := FixedArrayTable n (State k)
abbrev Row (n : ℕ) := FixedArrayTable n ℕ

def snapshots {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (fields : Fields n k) : FixedArrayTable n (Snapshot k) :=
  FixedArrayTable.ofFn (fun j => take prepared (fields.read j))

structure Selection {n k : ℕ} (fields : Fields n k) where
  candidateIndices : Row n
  responseIndices : Row n
  candidateValid : ∀ j, candidateIndices.read j<(fields.read j).plan.candidateCount
  responseValid : ∀ j, responseIndices.read j<(fields.read j).plan.responseCount

def Selection.choice {n k : ℕ} {fields : Fields n k} (selection : Selection fields) (j : Fin n) : Choice (fields.read j).plan :=
  ⟨⟨selection.candidateIndices.read j,selection.candidateValid j⟩,⟨selection.responseIndices.read j,selection.responseValid j⟩⟩

def Selection.candidateRow {n k : ℕ} {fields : Fields n k} (selection : Selection fields) : Row n :=
  FixedArrayTable.ofFn (fun j => (selection.choice j).candidateBid)

def Selection.responseRow {n k : ℕ} {fields : Fields n k} (selection : Selection fields) : Row n :=
  FixedArrayTable.ofFn (fun j => (selection.choice j).responseBid)

abbrev Selector (n k : ℕ) := (fields : Fields n k) → FixedArrayTable n (Snapshot k) → Selection fields

structure RoundResult (n k : ℕ) where
  fields : Fields n k
  candidate : Row n
  response : Row n

def round {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (fields : Fields n k) : RoundResult n k :=
  let before := snapshots prepared fields
  let selection := select fields before
  let candidate := selection.candidateRow
  let response := selection.responseRow
  let after := FixedArrayTable.ofFn (fun j => advance (fields.read j)
    (generate (fields.read j) (before.read j) (selection.choice j)).1)
  ⟨after,candidate,response⟩

theorem round_field {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (fields : Fields n k) (j : Fin n) :
    (round prepared select fields).fields.read j=
      GeneralPaperEpochFieldStep.step prepared (fields.read j) ((select fields (snapshots prepared fields)).choice j) := by
  simp only [round,FixedArrayTable.read_ofFn,snapshots,GeneralPaperEpochFieldStep.step]

theorem round_plan {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (fields : Fields n k) (j : Fin n) :
    ((round prepared select fields).fields.read j).plan=(fields.read j).plan := by
  rw [round_field,GeneralPaperEpochFieldStep.step_plan]

theorem round_candidate {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (fields : Fields n k) (j : Fin n) :
    (round prepared select fields).candidate.read j=
      ((select fields (snapshots prepared fields)).choice j).candidateBid := by
  exact FixedArrayTable.read_ofFn _ j

theorem round_response {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (fields : Fields n k) (j : Fin n) :
    (round prepared select fields).response.read j=
      ((select fields (snapshots prepared fields)).choice j).responseBid := by
  exact FixedArrayTable.read_ofFn _ j

def initial {n k : ℕ} (plans : FixedArrayTable n (GeneralPaperEpochFieldPlan.Plan k)) : Fields n k :=
  FixedArrayTable.ofFn (fun j => GeneralPaperEpochFieldState.initial (plans.read j))

def execute {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (first : Fields n k) :
    ℕ → Fields n k × Array (Row n)
  | 0 => (first,#[])
  | t+1 =>
    let previous := execute prepared select first t
    let next := round prepared select previous.1
    (next.fields,previous.2.push next.candidate)

theorem execute_step {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (first : Fields n k) (t : ℕ) :
    (execute prepared select first (t+1)).1=(round prepared select (execute prepared select first t).1).fields := rfl

theorem record_preupdate {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (first : Fields n k) (t : ℕ) :
    (execute prepared select first (t+1)).2=(execute prepared select first t).2.push
      (select (execute prepared select first t).1 (snapshots prepared (execute prepared select first t).1)).candidateRow := rfl

theorem trajectory_size {n k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (select : Selector n k) (first : Fields n k) (t : ℕ) :
    (execute prepared select first t).2.size=t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [execute,Array.size_push,ih]

end Blotto.GeneralPaperAdaptiveEpoch
