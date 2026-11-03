import Blotto.GeneralPaperScoreConstructionStorage

/-! Actual caller-frame metadata for the recursive stored score DP. A
completed lower layer is released after its one successor is constructed;
only the previous table and new prefix enter each active layer window.
Caller work counters are encoded through word lengths, never charged as
the whole DP time in storage. Matrix residency is a separate phase join. -/
namespace Blotto.GeneralPaperScoreLifetimeStorage
open GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperScoreConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def workCap (model : RationalCostModel) (W K S A r : ℕ) : ℕ :=
  GeneralPaperScoreDPBits.profile r K S W (model.rat (GeneralPaperScoreBitPrimitive.resourceWidth A r))

theorem run_work_bound {K : ℕ} (model : RationalCostModel) (W S A r : ℕ) (inputs : List (Field K))
    (hFields : CostHeight inputs A) (hLen : inputs.length≤r) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (GeneralPaperScoreDPBits.runWithBits model W S inputs).2≤workCap model W K S A r := by
  have hp := GeneralPaperScoreDPBits.run_work model W A S inputs hFields hW hIndex
  have hStep := GeneralPaperScoreDPBits.stepProfile_mono K S W (model.monotone
    (GeneralPaperScoreBitPrimitive.resourceWidth_mono A hLen))
  apply hp.trans
  unfold workCap GeneralPaperScoreDPBits.profile
  exact Nat.add_le_add_left (Nat.mul_le_mul hLen (Nat.add_le_add_right hStep (4*W))) _

def callerFrames {K : ℕ} (model : RationalCostModel) (W S : ℕ) : List (Field K) → ℕ
  | [] => fields W [0,(GeneralPaperScoreDPBits.runWithBits model W S ([] : List (Field K))).2]+128*W
  | f::rest => fields W [(f::rest).length,(GeneralPaperScoreDPBits.runWithBits model W S (f::rest)).2]+128*W+
      callerFrames model W S rest

def callerProfile (model : RationalCostModel) (W K S A r : ℕ) : ℕ :=
  (r+1)*(2*(natBits (r+workCap model W K S A r)+W)+160*W)

theorem caller_bound {K : ℕ} (model : RationalCostModel) (W S A r : ℕ) (inputs : List (Field K))
    (hFields : CostHeight inputs A) (hLen : inputs.length≤r) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    callerFrames model W S inputs≤(inputs.length+1)*(2*(natBits (r+workCap model W K S A r)+W)+160*W) := by
  have frame_bound (xs : List (Field K)) (hx : CostHeight xs A) (hl : xs.length≤r) :
      fields W [xs.length,(GeneralPaperScoreDPBits.runWithBits model W S xs).2]+128*W≤
      2*(natBits (r+workCap model W K S A r)+W)+160*W := by
    have hw := run_work_bound model W S A r xs hx hl hW hIndex
    have hp := two_fields_bound W (r+workCap model W K S A r) xs.length
      (GeneralPaperScoreDPBits.runWithBits model W S xs).2
      (hl.trans (Nat.le_add_right _ _)) (hw.trans (Nat.le_add_left _ _))
    exact (Nat.add_le_add_right hp (128*W)).trans_eq (by ring)
  induction inputs with
  | nil => simpa only [callerFrames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound [] hFields hLen
  | cons f rest ih =>
    have hf := frame_bound (f::rest) hFields hLen
    have hr := ih (fun g hg => hFields g (List.mem_cons_of_mem _ hg)) (by simp only [List.length_cons] at hLen; omega)
    simp only [Nat.add_mul,Nat.one_mul] at hr
    change GeneralPaperEncodedScalarStorage.fields W _+128*W+callerFrames model W S rest≤_
    simp only [List.length_cons] at hf
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem caller_profile {K : ℕ} (model : RationalCostModel) (W S A r : ℕ) (inputs : List (Field K))
    (hFields : CostHeight inputs A) (hLen : inputs.length≤r) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    callerFrames model W S inputs≤callerProfile model W K S A r :=
  (caller_bound model W S A r inputs hFields hLen hW hIndex).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hLen 1))

def layerProfile (model : RationalCostModel) (W K S A r : ℕ) : ℕ :=
  callerProfile model W K S A r+stepProfile model W K S A r

theorem actual_layer {K S : ℕ} (model : RationalCostModel) (W A r : ℕ) (inputs : List (Field K))
    (hFields : CostHeight inputs A) (hLen : inputs.length≤r) (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W)
    (field : Field K) (rest : List (Field K)) (hSub : (field::rest).Sublist inputs)
    (count : ℕ) (hc : count≤S+1) (s : Fin (S+1)) (xs : List (Fin K)) (hXs : xs.length≤K) :
    callerFrames model W S inputs+stepWindow model W field rest count hc s xs≤layerProfile model W K S A r := by
  have hLocal : CostHeight (field::rest) A := fun f hf => hFields f (hSub.subset hf)
  have hLocalLen : rest.length+1≤r := hSub.length_le.trans hLen
  exact Nat.add_le_add (caller_profile model W S A r inputs hFields hLen hW hIndex)
    (step_bound model W A r field rest hLocal hLocalLen hW hIndex count hc s xs hXs)

end Blotto.GeneralPaperScoreLifetimeStorage
