import Blotto.GeneralPaperEqualFinalClosureCaller

/-! One analysis capacity for native segment construction through the final
returned sampler, including budget/address/control and all work records.
Initial prefix construction and the program-computed common word remain
open, so this is not yet whole-preparation working-space capacity. -/
namespace Blotto.GeneralPaperEqualFinalClosureCapacity
open GeneralPaperReferenceScaling
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

@[fun_prop]
theorem budget_scan_scale (model : RationalCostModel) (b : ℕ) :
    Scale (fun A => GeneralPaperWordLengthLifetime.rationalProfile model A b) := by
  unfold GeneralPaperWordLengthLifetime.rationalProfile
  fun_prop

@[fun_prop]
theorem address_scale (model : RationalCostModel) (n m k b : ℕ) :
    Scale (fun A => GeneralPaperAddressConstructionLifetime.profile model A n m k b) := by
  unfold GeneralPaperAddressConstructionLifetime.profile
  fun_prop

@[fun_prop]
theorem time_scale (model : RationalCostModel) (n m k b : ℕ) :
    Scale (fun A => GeneralPaperEqualFinalClosureLifetime.time model A n m k b) := by
  unfold GeneralPaperEqualFinalClosureLifetime.time
  fun_prop

@[fun_prop]
theorem control_scale (model : RationalCostModel) (n m k b : ℕ) :
    Scale (fun A => GeneralPaperEqualFinalClosureLifetime.controlProfile model A n m k b) := by
  unfold GeneralPaperEqualFinalClosureLifetime.controlProfile
  fun_prop

@[fun_prop]
theorem returned_scale (n k b : ℕ) :
    Scale (fun A => GeneralPaperEqualNativeRetainedStorage.profile A n k b) := by
  unfold GeneralPaperEqualNativeRetainedStorage.profile GeneralPaperEqualRetainedStorage.preparedProfile GeneralPaperEqualRetainedStorage.cacheProfile GeneralPaperEqualRetainedStorage.wordProfile GeneralPaperEqualRetainedStorage.segmentProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

theorem borrowed_scale {n : ℕ} (model : RationalCostModel) (W exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualFinalClosureCaller.borrowedProfile model W A exponent c width values budget) := by
  have hPrevious := GeneralPaperEqualBooleanCapacity.native_scale model W exponent c width values budget
  have hLedger := GeneralPaperEqualSegmentCallerCapacity.ledger_scale model W exponent values (rationalWordWidth budget)
  unfold GeneralPaperEqualFinalClosureCaller.borrowedProfile GeneralPaperEqualFinalClosureCaller.workProfile
  fun_prop

theorem kernel_scale (model : RationalCostModel) (n m k b : ℕ) (borrowed returned : ℕ → ℕ)
    (hb : Scale borrowed) (hr : Scale returned) :
    Scale (fun A => GeneralPaperEqualFinalClosureLifetime.profile model A n m k b (borrowed A) (returned A)) := by
  unfold GeneralPaperEqualFinalClosureLifetime.profile
  fun_prop

theorem native_scale {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualFinalClosureCaller.profile model W A exponent m c width values budget) :=
  kernel_scale model n m exponent (rationalWordWidth budget) _ _
    (borrowed_scale model W exponent c width values budget) (returned_scale n exponent (rationalWordWidth budget))

def Phase (m c K width : ℕ) := Sum (GeneralPaperEqualBooleanCapacity.Phase m c K width) GeneralPaperEqualFinalClosureLifetime.Phase

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase (terminal (rounded bits model W exponent values v hv) small).groups.length
      (count (lottery (rounded bits model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare bits model W exponent values v hv small budget).rangeBits → ℕ
  | .inl phase => GeneralPaperEqualBooleanCapacity.window bits model W A exponent values v hv small budget phase
  | .inr phase => GeneralPaperEqualFinalClosureCaller.window bits model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualBooleanCapacity.profile model W A exponent c width values budget)
    (GeneralPaperEqualFinalClosureCaller.profile model W A exponent m c width values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (terminal (rounded true model W exponent values v hv) small).groups.length
        (count (lottery (rounded true model W exponent values v hv) small))
        (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits values budget := by
  cases phase with
  | inl phase =>
    exact (GeneralPaperEqualBooleanCapacity.all_phases model W A exponent values v hv small budget phase).trans (le_max_left _ _)
  | inr phase =>
    exact (GeneralPaperEqualFinalClosureCaller.all_phases model W A exponent values v hv small budget phase).trans (le_max_right _ _)

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A exponent m c width values budget) := by
  have hEarlier := GeneralPaperEqualBooleanCapacity.combined_scale model W exponent c width values budget
  have hFinal := native_scale model W exponent m c width values budget
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
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    let m := (terminal (rounded true model W exponent values v hv) small).groups.length
    let c := count (lottery (rounded true model W exponent values v hv) small)
    let width := (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits
    let A := reference model W exponent m c width values budget
    window true model W A exponent values v hv small budget phase < 2 ^ A := by
  let m := (terminal (rounded true model W exponent values v hv) small).groups.length
  let c := count (lottery (rounded true model W exponent values v hv) small)
  let width := (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits
  let A := reference model W exponent m c width values budget
  exact (all_phases model W A exponent values v hv small budget phase).trans_lt (capacity model W exponent m c width values budget)

end Blotto.GeneralPaperEqualFinalClosureCapacity
