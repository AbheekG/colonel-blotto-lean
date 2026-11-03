import Blotto.GeneralPaperFixedViolationPrice

/-! Recover the actual original row by one shape check and sequential
reference-buffer materialization of the shared label list. The guard and
all input/output traversal traffic are included; no tuple search is run.
-/
namespace Blotto.GeneralPaperFixedTupleDecodePrice
open GeneralPaperRayAffineMinimum
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {K : ℕ} (indexPrimitive : ℕ → ℕ) (W m : ℕ) (chosen : Choice K) :
    Option (FixedArrayTable m (Fin K)) × ℕ :=
  if hLength : chosen.labels.length=m then
    let materialized := PaperListReferenceArray.run indexPrimitive W chosen.labels
    (some ⟨materialized.1,by rw [PaperListReferenceArray.size,hLength]⟩,
      materialized.2+(8*chosen.labels.length+16)*W)
  else (none,(8*chosen.labels.length+16)*W)

theorem data {K : ℕ} (indexPrimitive : ℕ → ℕ) (W m : ℕ) (chosen : Choice K) :
    (run indexPrimitive W m chosen).1=GeneralPaperRayFixedTuple.decode m chosen := by
  simp only [run,GeneralPaperRayFixedTuple.decode,PaperListReferenceArray.data]
  split <;> rfl

theorem bit_work {K : ℕ} (W m : ℕ) (chosen : Choice K) (hW : 1≤W)
    (hIndex : binaryWordWidth (chosen.labels.length+1)≤W) :
    (run (fun w => w) W m chosen).2≤96*(chosen.labels.length+1)*W := by
  have ha := PaperListReferenceArray.bit_work W chosen.labels hW hIndex
  rw [run]
  split <;> dsimp only
  · nlinarith only [ha]
  · nlinarith

theorem arithmetic_work {K : ℕ} (m : ℕ) (chosen : Choice K) :
    (run (fun _ => 1) 1 m chosen).2≤96*(chosen.labels.length+1) := by
  have ha := PaperListReferenceArray.arithmetic_work chosen.labels
  rw [run]
  split <;> dsimp only
  · nlinarith only [ha]
  · omega

end Blotto.GeneralPaperFixedTupleDecodePrice
