import Blotto.GeneralPaperEqualPackingCallerLifetime

/-! Shared analysis capacity now includes the native packing reserve,
initial rounding/length phases and later segment-through-return phases.
Route construction and the program-computed common word remain open. -/
namespace Blotto.GeneralPaperEqualPackingCapacity
open GeneralPaperReferenceScaling
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

@[fun_prop]
theorem unit_scale (n : ℕ) : Scale (fun A => GeneralPaperEqualPackingExecution.unit A n) := by
  unfold GeneralPaperEqualPackingExecution.unit
  fun_prop

@[fun_prop]
theorem frame_scale (n : ℕ) (F : ℕ → ℕ) (hF : Scale F) :
    Scale (fun A => GeneralPaperPackingFrameLifetime.frameProfile A n (F A)) := by
  unfold GeneralPaperPackingFrameLifetime.frameProfile
  fun_prop

@[fun_prop]
theorem pool_scale (n : ℕ) : Scale (fun A => GeneralPaperPackingAllocationLifetime.poolProfile A n) := by
  unfold GeneralPaperPackingAllocationLifetime.poolProfile
  fun_prop

@[fun_prop]
theorem indices_scale (n : ℕ) : Scale (fun A => GeneralPaperPackingAllocationLifetime.indicesProfile A n) := by
  unfold GeneralPaperPackingAllocationLifetime.indicesProfile
  fun_prop

theorem kernel_scale (n : ℕ) (F borrowed returned : ℕ → ℕ) (hF : Scale F) (hB : Scale borrowed) (hR : Scale returned) :
    Scale (fun A => GeneralPaperPackingLifetime.profile A n (F A) (borrowed A) (returned A)) := by
  unfold GeneralPaperPackingLifetime.profile
  fun_prop

@[fun_prop]
theorem packed_owner_scale (n m s : ℕ) : Scale (fun A => GeneralPaperEqualPackedOwner.profile A n m s) := by
  unfold GeneralPaperEqualPackedOwner.profile
  fun_prop

theorem native_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualPackingCallerLifetime.profile model W A exponent values budget) :=
  kernel_scale n _ _ _
    (GeneralPaperEqualSegmentCallerCapacity.ledger_scale model W exponent values (rationalWordWidth budget))
    (GeneralPaperEqualInitialPrefixCapacity.prefix_scale model W exponent values budget)
    (packed_owner_scale n 3 (binaryWordWidth n + exponent + 9))

def Phase (n m c K width : ℕ) := Option (GeneralPaperEqualInitialPrefixCapacity.Phase n m c K width)

def window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase n (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits → ℕ
  | none => GeneralPaperEqualPackingCallerLifetime.window model W A exponent values v hv small budget
  | some phase => GeneralPaperEqualInitialPrefixCapacity.window model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualInitialPrefixCapacity.profile model W A exponent m c width values budget)
    (GeneralPaperEqualPackingCallerLifetime.profile model W A exponent values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase n (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    window model W A exponent values v hv small budget phase ≤
      profile model W A exponent (terminal (rounded true model W exponent values v hv) small).groups.length
        (count (lottery (rounded true model W exponent values v hv) small))
        (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits values budget := by
  cases phase with
  | none => exact (GeneralPaperEqualPackingCallerLifetime.actual model W A exponent values v hv small budget).trans (le_max_right _ _)
  | some phase => exact (GeneralPaperEqualInitialPrefixCapacity.all_phases model W A exponent values v hv small budget phase).trans (le_max_left _ _)

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A exponent m c width values budget) := by
  have hEarlier := GeneralPaperEqualInitialPrefixCapacity.combined_scale model W exponent m c width values budget
  have hPacking := native_scale model W exponent values budget
  unfold profile
  fun_prop

def reference {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (profile model W 1 exponent m c width values budget)

theorem capacity {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W exponent m c width values budget
    profile model W A exponent m c width values budget < 2 ^ A :=
  GeneralPaperReferenceCapacity.profile_capacity (fun A => profile model W A exponent m c width values budget)
    (combined_scale model W exponent m c width values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase n (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    let m := (terminal (rounded true model W exponent values v hv) small).groups.length
    let c := count (lottery (rounded true model W exponent values v hv) small)
    let width := (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits
    let A := reference model W exponent m c width values budget
    window model W A exponent values v hv small budget phase < 2 ^ A := by
  let m := (terminal (rounded true model W exponent values v hv) small).groups.length
  let c := count (lottery (rounded true model W exponent values v hv) small)
  let width := (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits
  let A := reference model W exponent m c width values budget
  exact (all_phases model W A exponent values v hv small budget phase).trans_lt (capacity model W exponent m c width values budget)

end Blotto.GeneralPaperEqualPackingCapacity
