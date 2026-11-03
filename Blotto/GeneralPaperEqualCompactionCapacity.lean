import Blotto.GeneralPaperEqualMiddlePreparationLifetime

/-! Reference scaling and one analysis capacity for the actual native
segment/compaction/integer phases. W stays fixed. The program-computed
whole-preparation common word and the remaining phases are still open. -/
namespace Blotto.GeneralPaperEqualCompactionCapacity
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

@[fun_prop]
theorem scan_step_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperPositiveLabelScan.stepBound model A r s) := by
  unfold GeneralPaperPositiveLabelScan.stepBound
  fun_prop

@[fun_prop]
theorem indices_scale (r : ℕ) :
    Scale (fun A => GeneralPaperEqualRouteConstruction.indicesWork A r) := by
  unfold GeneralPaperEqualRouteConstruction.indicesWork
  fun_prop

@[fun_prop]
theorem selection_time_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperPreparedPositiveLabels.bound model A r s) := by
  unfold GeneralPaperPreparedPositiveLabels.bound
  fun_prop

@[fun_prop]
theorem label_scale (length r : ℕ) :
    Scale (fun A => GeneralPaperPositiveScanLifetime.labelProfile A length r) := by
  unfold GeneralPaperPositiveScanLifetime.labelProfile
  fun_prop

@[fun_prop]
theorem selection_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperPositiveSelectionLifetime.profile model A r s) := by
  unfold GeneralPaperPositiveSelectionLifetime.profile
  dsimp only
  fun_prop

@[fun_prop]
theorem item_time_scale (r s : ℕ) :
    Scale (fun A => GeneralPaperPreparedSegmentCompaction.itemBound A r s) := by
  unfold GeneralPaperPreparedSegmentCompaction.itemBound
  fun_prop

@[fun_prop]
theorem make_time_scale (r s : ℕ) :
    Scale (fun A => GeneralPaperPreparedSegmentCompaction.makeBound A r s) := by
  unfold GeneralPaperPreparedSegmentCompaction.makeBound
  fun_prop

@[fun_prop]
theorem total_time_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperPreparedSegmentCompaction.bound model A r s) := by
  unfold GeneralPaperPreparedSegmentCompaction.bound
  fun_prop

@[fun_prop]
theorem lookup_scale (r : ℕ) :
    Scale (fun A => GeneralPaperCompactionCallbackLifetime.lookupProfile A r) := by
  unfold GeneralPaperCompactionCallbackLifetime.lookupProfile
  fun_prop

@[fun_prop]
theorem callback_scale (r s : ℕ) :
    Scale (fun A => GeneralPaperCompactionCallbackLifetime.profile A r s) := by
  unfold GeneralPaperCompactionCallbackLifetime.profile
  fun_prop

@[fun_prop]
theorem array_time_scale (c r s : ℕ) :
    Scale (fun A => GeneralPaperCompactionArrayLifetime.arrayTime A c r s) := by
  unfold GeneralPaperCompactionArrayLifetime.arrayTime
  fun_prop

@[fun_prop]
theorem array_owner_scale (c r s : ℕ) :
    Scale (fun A => GeneralPaperCompactionArrayLifetime.ownerProfile A c r s) := by
  unfold GeneralPaperCompactionArrayLifetime.ownerProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem selection_owner_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperCompactionArrayLifetime.selectionProfile model A r s) := by
  unfold GeneralPaperCompactionArrayLifetime.selectionProfile
  fun_prop

@[fun_prop]
theorem control_scale (model : RationalCostModel) (r s : ℕ) :
    Scale (fun A => GeneralPaperCompactionLifetime.controlProfile model A r s) := by
  unfold GeneralPaperCompactionLifetime.controlProfile
  fun_prop

theorem kernel_scale (model : RationalCostModel) (c r s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperCompactionLifetime.profile model A c r s (borrowed A)) := by
  unfold GeneralPaperCompactionLifetime.profile GeneralPaperCompactionArrayLifetime.residentProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

theorem native_scale {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualCompactionCallerLifetime.profile model W A exponent c values budget) :=
  kernel_scale model c 9 _ _ (GeneralPaperEqualIntegerCallerCapacity.resident_scale model W exponent values budget)

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ)
    (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualMiddlePreparationLifetime.profile model W A exponent c values budget) := by
  have hSegment := GeneralPaperEqualSegmentCallerCapacity.profile_scale model W exponent values budget
  have hCompact := native_scale model W exponent c values budget
  have hInteger := GeneralPaperEqualIntegerCallerCapacity.profile_scale model W exponent c values budget
  unfold GeneralPaperEqualMiddlePreparationLifetime.profile
  fun_prop

def reference {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (GeneralPaperEqualMiddlePreparationLifetime.profile model W 1 exponent c values budget)

theorem capacity {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W exponent c values budget
    GeneralPaperEqualMiddlePreparationLifetime.profile model W A exponent c values budget < 2 ^ A :=
  GeneralPaperReferenceCapacity.profile_capacity
    (fun A => GeneralPaperEqualMiddlePreparationLifetime.profile model W A exponent c values budget)
    (combined_scale model W exponent c values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (phase : GeneralPaperEqualMiddlePreparationLifetime.Phase
      (GeneralPaperEqualFiniteKernel.terminal (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small).groups.length
      (GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
        (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small))) :
    let c := GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
      (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small)
    let A := reference model W exponent c values budget
    GeneralPaperEqualMiddlePreparationLifetime.window true model W A exponent values v hv small budget phase < 2 ^ A := by
  let c := GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery
    (GeneralPaperEqualNativeSampler.rounded true model W exponent values v hv) small)
  let A := reference model W exponent c values budget
  exact (GeneralPaperEqualMiddlePreparationLifetime.all_phases model W A exponent values v hv small budget phase).trans_lt
    (capacity model W exponent c values budget)

end Blotto.GeneralPaperEqualCompactionCapacity
