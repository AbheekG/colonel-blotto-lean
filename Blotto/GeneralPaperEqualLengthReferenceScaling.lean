import Blotto.GeneralPaperEqualLengthPhaseStorage

/-! Reference-width scaling and capacity for the proved length-construction
callback windows. This is a phase profile, not a whole-preparation reserve or
a claim that the program has computed the final common reference word. -/
namespace Blotto.GeneralPaperEqualLengthReferenceScaling
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 1400000

@[fun_prop]
theorem overhead_scale (primitive : ℕ → ℕ) (count k : ℕ) :
    Scale (fun A => PaperIndexedArrayConstruction.overhead primitive A count k) := by
  induction k with
  | zero =>
    unfold PaperIndexedArrayConstruction.overhead PaperIndexedArrayConstruction.initialWork
    fun_prop
  | succ k ih =>
    unfold PaperIndexedArrayConstruction.overhead PaperIndexedArrayConstruction.stepWork
    fun_prop

@[fun_prop]
theorem loop_scale (model : RationalCostModel) (n s : ℕ) :
    Scale (fun A => GeneralPaperEqualLengthPhaseStorage.loopProfile model A n s) := by
  unfold GeneralPaperEqualLengthPhaseStorage.loopProfile
  fun_prop

@[fun_prop]
theorem frame_scale (n : ℕ) (f : ℕ → ℕ) (hf : Scale f) :
    Scale (fun A => GeneralPaperIndexedArrayLifetime.frame A n (f A)) := by
  unfold GeneralPaperIndexedArrayLifetime.frame
  fun_prop

theorem profile_scale (model : RationalCostModel) (n s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperEqualLengthPhaseStorage.profile model A n s (borrowed A)) := by
  unfold GeneralPaperEqualLengthPhaseStorage.profile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

def reference (model : RationalCostModel) (n s : ℕ) (borrowed : ℕ → ℕ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (GeneralPaperEqualLengthPhaseStorage.profile model 1 n s (borrowed 1))

theorem capacity (model : RationalCostModel) (n s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    GeneralPaperEqualLengthPhaseStorage.profile model (reference model n s borrowed) n s
      (borrowed (reference model n s borrowed)) < 2 ^ reference model n s borrowed :=
  GeneralPaperReferenceCapacity.profile_capacity _ (profile_scale model n s borrowed hb)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (D s : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : 2 ≤ s) (hD : binaryWordWidth D ≤ s) (ha : ∀ j, weights.read j ≤ D)
    (k : ℕ) (hk : k < n) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    let A := reference model n s borrowed
    GeneralPaperEqualLengthPhaseStorage.phaseWindow model A weights D k hk (borrowed A) < 2 ^ A :=
  (GeneralPaperEqualLengthPhaseStorage.actual model _ D s weights hs hD ha k hk _).trans_lt
    (capacity model n s borrowed hb)

end Blotto.GeneralPaperEqualLengthReferenceScaling
