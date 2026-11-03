import Blotto.GeneralPaperEqualIntegerCallerLifetime

/-! Integer-data phase capacity includes the actual proved original/prefix,
full/compact descriptor and work-record owners. Input word W is fixed; the
reference here is analysis-only until the whole-preparation construction. -/
namespace Blotto.GeneralPaperEqualIntegerCallerCapacity
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 2000000

@[fun_prop]
theorem product_time_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperCategoricalIntegerLifetime.productTime model A r s) := by
  unfold GeneralPaperCategoricalIntegerLifetime.productTime GeneralPaperStoredCategoricalProduct.stepBound
  fun_prop

@[fun_prop]
theorem count_step_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperStoredCategoricalCounts.stepBound model A r s) := by
  unfold GeneralPaperStoredCategoricalCounts.stepBound
  fun_prop

@[fun_prop]
theorem array_time_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperCategoricalIntegerLifetime.arrayTime model A r s) := by
  unfold GeneralPaperCategoricalIntegerLifetime.arrayTime
  fun_prop

@[fun_prop]
theorem total_time_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperCategoricalIntegerLifetime.totalTime model A r s) := by
  unfold GeneralPaperCategoricalIntegerLifetime.totalTime
  fun_prop

theorem kernel_scale (model : RationalCostModel) (r s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperCategoricalIntegerLifetime.profile model A r s (borrowed A)) := by
  unfold GeneralPaperCategoricalIntegerLifetime.profile GeneralPaperCategoricalIntegerLifetime.productOwnerProfile
    GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

theorem resident_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualIntegerCallerLifetime.residentProfile model W A exponent values budget) := by
  have hOwner := GeneralPaperEqualSegmentCallerCapacity.owner_scale model W exponent values budget
  have hLedger := GeneralPaperEqualSegmentCallerCapacity.ledger_scale model W exponent values (rationalWordWidth budget)
  unfold GeneralPaperEqualIntegerCallerLifetime.residentProfile GeneralPaperEqualRetainedStorage.segmentProfile
    GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

theorem profile_scale {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualIntegerCallerLifetime.profile model W A exponent values budget c) :=
  kernel_scale model c _ _ (resident_scale model W exponent values budget)

def reference {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (GeneralPaperEqualIntegerCallerLifetime.profile model W 1 exponent values budget c)

theorem capacity {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W exponent c values budget
    GeneralPaperEqualIntegerCallerLifetime.profile model W A exponent values budget c < 2 ^ A :=
  GeneralPaperReferenceCapacity.profile_capacity _ (profile_scale model W exponent c values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (phase : GeneralPaperCategoricalIntegerLifetime.Phase (GeneralPaperPositiveSegmentCompaction.count
      (GeneralPaperEqualFiniteKernel.lottery (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small))) :
    let c := GeneralPaperPositiveSegmentCompaction.count
      (GeneralPaperEqualFiniteKernel.lottery (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small)
    let A := reference model W exponent c values budget
    GeneralPaperEqualIntegerCallerLifetime.window true model W A exponent values v hv small budget phase < 2 ^ A :=
  (GeneralPaperEqualIntegerCallerLifetime.all_phases model W _ exponent values v hv small budget phase).trans_lt
    (capacity model W exponent _ values budget)

end Blotto.GeneralPaperEqualIntegerCallerCapacity
