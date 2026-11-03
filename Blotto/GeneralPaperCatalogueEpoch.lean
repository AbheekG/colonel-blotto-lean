import Blotto.GeneralPaperCatalogueEpochRows

/-! An inhabited four-family epoch using both actual native catalogue
optimizers. Each round computes one common snapshot, chooses the two complete
rows, records the candidate before updating, and sends exactly those choices
to all eight generated delta arrays. Constructed plans persist by type.
-/
namespace Blotto.GeneralPaperCatalogueEpoch
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows
open GeneralPaperCatalogueRowSemantics
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

structure RoundResult {m k : ℕ} (cache : Cache m k) where
  state : State cache
  candidate : FixedArrayTable m ℕ
  response : FixedArrayTable m ℕ

def round {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (state : State cache) : RoundResult cache :=
  let before := GeneralPaperAdaptiveEpoch.snapshots powers state.fields
  let rows := chooseRows cache profit T weights before Bc Br
  let fields := FixedArrayTable.ofFn (fun j => GeneralPaperEpochFieldState.advance (state.fields.read j)
    (GeneralPaperEpochDeltas.generate (state.fields.read j) (before.read j) (rows.fieldChoice state j)).1)
  ⟨⟨fields,by intro j; rw [FixedArrayTable.read_ofFn,GeneralPaperEpochFieldState.advance_plan,state.plan_spec]⟩,
    rowCodes cache.candidate.data rows.candidate,rowCodes cache.response.data rows.response⟩

theorem round_field {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (state : State cache) (j : Fin m) :
    ((round cache powers profit T weights Bc Br state).state.fields.read j)=
      GeneralPaperEpochFieldStep.step powers (state.fields.read j)
        ((chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).fieldChoice state j) := by
  simp only [round,FixedArrayTable.read_ofFn,GeneralPaperAdaptiveEpoch.snapshots,GeneralPaperEpochFieldStep.step]

theorem round_candidate {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (state : State cache) (j : Fin m) :
    (round cache powers profit T weights Bc Br state).candidate.read j=
      ((chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).fieldChoice state j).candidateBid :=
  (field_candidate _ state j).symm

theorem round_response {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (state : State cache) (j : Fin m) :
    (round cache powers profit T weights Bc Br state).response.read j=
      ((chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).fieldChoice state j).responseBid :=
  (field_response _ state j).symm

def execute {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) :
    ℕ → State cache × Array (FixedArrayTable m ℕ)
  | 0 => (first,#[])
  | t+1 =>
    let previous := execute cache powers profit T weights Bc Br first t
    let next := round cache powers profit T weights Bc Br previous.1
    (next.state,previous.2.push next.candidate)

theorem execute_step {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (t : ℕ) :
    (execute cache powers profit T weights Bc Br first (t+1)).1=
      (round cache powers profit T weights Bc Br (execute cache powers profit T weights Bc Br first t).1).state := rfl

theorem record_preupdate {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (t : ℕ) :
    (execute cache powers profit T weights Bc Br first (t+1)).2=
      (execute cache powers profit T weights Bc Br first t).2.push
        (round cache powers profit T weights Bc Br (execute cache powers profit T weights Bc Br first t).1).candidate := rfl

theorem trajectory_size {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (t : ℕ) :
    (execute cache powers profit T weights Bc Br first t).2.size=t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [execute,Array.size_push,ih]

theorem trajectory_read {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache)
    (count time : ℕ) (hTime : time<count) :
    (execute cache powers profit T weights Bc Br first count).2[time]'(by rw [trajectory_size]; exact hTime)=
      (round cache powers profit T weights Bc Br (execute cache powers profit T weights Bc Br first time).1).candidate := by
  induction count with
  | zero => omega
  | succ count ih =>
    change ((execute cache powers profit T weights Bc Br first count).2.push
      (round cache powers profit T weights Bc Br (execute cache powers profit T weights Bc Br first count).1).candidate)[time]'(by
        rw [Array.size_push,trajectory_size]; exact hTime)=_
    rw [Array.getElem_push]
    split_ifs with h
    · exact ih (by rw [trajectory_size] at h; exact h)
    · have he : time=count := by rw [trajectory_size] at h; omega
      subst time
      rfl

end Blotto.GeneralPaperCatalogueEpoch
