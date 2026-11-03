import Blotto.GeneralPaperEqualSegmentCallerLifetime

/-! Capacity now includes the proved original/prefix/code caller owners,
not an arbitrary borrowed-size premise. Input-word W is held fixed; this
analysis reference is not yet the computed whole-preparation common word. -/
namespace Blotto.GeneralPaperEqualSegmentCallerCapacity
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 2000000

@[fun_prop]
theorem ledger_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (b : ℕ) :
    Scale (fun A => GeneralPaperEqualBitPreparationLedger.profile model W A exponent values b) := by
  unfold GeneralPaperEqualBitPreparationLedger.profile GeneralPaperEqualPackingExecution.unit
  fun_prop

theorem owner_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualSegmentCallerLifetime.ownerProfile model W A exponent values budget) := by
  unfold GeneralPaperEqualSegmentCallerLifetime.ownerProfile GeneralPaperEqualSegmentCallerOwners.profile
    GeneralPaperEqualPrefixOwners.roundedProfile GeneralPaperEqualPackedOwner.profile GeneralPaperEqualRouteOwner.profile
    GeneralPaperEqualStaticCodeOwner.profile GeneralPaperExpressionCodeOwner.unit
    GeneralPaperEqualSegmentCallerOwners.controlProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

theorem profile_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualSegmentCallerLifetime.profile model W A exponent values budget) := by
  have hOwner := owner_scale model W exponent values budget
  unfold GeneralPaperEqualSegmentCallerLifetime.profile
  exact GeneralPaperSegmentFactoryReferenceScaling.native_profile model _ _ hOwner

def reference {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (GeneralPaperEqualSegmentCallerLifetime.profile model W 1 exponent values budget)

theorem capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W exponent values budget
    GeneralPaperEqualSegmentCallerLifetime.profile model W A exponent values budget < 2 ^ A :=
  GeneralPaperReferenceCapacity.profile_capacity _ (profile_scale model W exponent values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small).groups.length) :
    let A := reference model W exponent values budget
    GeneralPaperEqualSegmentCallerLifetime.window true model W A exponent values v hv small budget phase < 2 ^ A :=
  (GeneralPaperEqualSegmentCallerLifetime.actual model W _ exponent values v hv small budget phase).trans_lt
    (capacity model W exponent values budget)

end Blotto.GeneralPaperEqualSegmentCallerCapacity
