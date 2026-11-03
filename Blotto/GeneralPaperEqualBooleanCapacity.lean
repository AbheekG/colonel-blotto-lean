import Blotto.GeneralPaperEqualBooleanCallerLifetime

/-! Reference scaling and shared analysis capacity through Boolean-cache
construction. Native phase widths are the canonical equal cache widths,
proved equal to the actual stored source; no width oracle is executed.
Final budget/address and initial prefix phases remain open. -/
namespace Blotto.GeneralPaperEqualBooleanCapacity
open GeneralPaperReferenceScaling
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (lottery terminal)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

@[fun_prop]
theorem word_step_scale (model : RationalCostModel) (width L : ℕ) :
    Scale (fun A => GeneralPaperStoredWordEncoding.stepBound model A width L) := by
  unfold GeneralPaperStoredWordEncoding.stepBound
  fun_prop

@[fun_prop]
theorem word_time_scale (model : RationalCostModel) (width L : ℕ) :
    Scale (fun A => GeneralPaperWordEncodingLifetime.time model A width L) := by
  unfold GeneralPaperWordEncodingLifetime.time
  fun_prop

@[fun_prop]
theorem bit_list_scale (width : ℕ) :
    Scale (fun A => GeneralPaperWordEncodingLifetime.bitListProfile A width) := by
  unfold GeneralPaperWordEncodingLifetime.bitListProfile
  fun_prop

@[fun_prop]
theorem word_live_scale (model : RationalCostModel) (width L : ℕ) :
    Scale (fun A => GeneralPaperWordEncodingLifetime.profile model A width L) := by
  unfold GeneralPaperWordEncodingLifetime.profile
  fun_prop

@[fun_prop]
theorem retained_word_scale (width : ℕ) :
    Scale (fun A => GeneralPaperEqualRetainedStorage.wordProfile A width) := by
  unfold GeneralPaperEqualRetainedStorage.wordProfile
  fun_prop

@[fun_prop]
theorem word_window_scale (model : RationalCostModel) (width L : ℕ) :
    Scale (fun A => GeneralPaperWordEncodingLifetime.windowProfile model A width L) := by
  unfold GeneralPaperWordEncodingLifetime.windowProfile
  fun_prop

@[fun_prop]
theorem row_time_scale (model : RationalCostModel) (c width L : ℕ) :
    Scale (fun A => GeneralPaperBooleanRowsLifetime.time model A c width L) := by
  unfold GeneralPaperBooleanRowsLifetime.time GeneralPaperStoredBooleanCache.rowBound
  fun_prop

@[fun_prop]
theorem row_entry_scale (c width : ℕ) :
    Scale (fun A => GeneralPaperBooleanRowsLifetime.entryProfile A c width) := by
  unfold GeneralPaperBooleanRowsLifetime.entryProfile
  fun_prop

@[fun_prop]
theorem row_list_scale (c width length : ℕ) :
    Scale (fun A => GeneralPaperBooleanRowsLifetime.listProfile A c width length) := by
  unfold GeneralPaperBooleanRowsLifetime.listProfile
  fun_prop

@[fun_prop]
theorem row_local_scale (model : RationalCostModel) (c width L : ℕ) :
    Scale (fun A => GeneralPaperBooleanRowsLifetime.localProfile model A c width L) := by
  unfold GeneralPaperBooleanRowsLifetime.localProfile
  fun_prop

@[fun_prop]
theorem rows_scale (model : RationalCostModel) (c width L : ℕ) :
    Scale (fun A => GeneralPaperBooleanRowsLifetime.profile model A c width L) := by
  unfold GeneralPaperBooleanRowsLifetime.profile
  fun_prop

@[fun_prop]
theorem cache_time_scale (model : RationalCostModel) (c width L : ℕ) :
    Scale (fun A => GeneralPaperStoredBooleanCache.bound model A c width L) := by
  unfold GeneralPaperStoredBooleanCache.bound GeneralPaperStoredBooleanCache.rowBound
  fun_prop

@[fun_prop]
theorem labels_scale (c : ℕ) :
    Scale (fun A => GeneralPaperBooleanCacheLifetime.labelsProfile A c) := by
  unfold GeneralPaperBooleanCacheLifetime.labelsProfile
  dsimp only
  fun_prop

@[fun_prop]
theorem ruler_scale (width : ℕ) :
    Scale (fun A => GeneralPaperBooleanCacheLifetime.rulerProfile A width) := by
  unfold GeneralPaperBooleanCacheLifetime.rulerProfile
  fun_prop

@[fun_prop]
theorem retained_cache_scale (c width : ℕ) :
    Scale (fun A => GeneralPaperEqualRetainedStorage.cacheProfile A c width) := by
  unfold GeneralPaperEqualRetainedStorage.cacheProfile
  fun_prop

@[fun_prop]
theorem controls_scale (model : RationalCostModel) (c width L : ℕ) :
    Scale (fun A => GeneralPaperBooleanCacheLifetime.controlProfile model A c width L) := by
  unfold GeneralPaperBooleanCacheLifetime.controlProfile
  fun_prop

theorem kernel_scale (model : RationalCostModel) (c width L : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperBooleanCacheLifetime.profile model A c width L (borrowed A)) := by
  unfold GeneralPaperBooleanCacheLifetime.profile
  fun_prop

theorem native_scale {n : ℕ} (model : RationalCostModel) (W exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualBooleanCallerLifetime.profile model W A exponent c width values budget) :=
  kernel_scale model c width _ _ (GeneralPaperEqualPowerWidthCapacity.native_scale model W exponent c values budget)

def Phase (m c K width : ℕ) := Sum (GeneralPaperEqualPowerWidthCapacity.Phase m c K) (GeneralPaperBooleanCacheLifetime.Phase width)

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase (terminal (rounded bits model W exponent values v hv) small).groups.length
      (count (lottery (rounded bits model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare bits model W exponent values v hv small budget).rangeBits → ℕ
  | .inl phase => GeneralPaperEqualPowerWidthCapacity.window bits model W A exponent values v hv small budget phase
  | .inr phase => GeneralPaperEqualBooleanCallerLifetime.window bits model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualPowerWidthCapacity.profile model W A exponent c values budget)
    (GeneralPaperEqualBooleanCallerLifetime.profile model W A exponent c width values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (count (lottery (rounded true model W exponent values v hv) small))
        (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits values budget := by
  cases phase with
  | inl phase =>
    exact (GeneralPaperEqualPowerWidthCapacity.all_phases model W A exponent values v hv small budget phase).trans (le_max_left _ _)
  | inr phase =>
    exact (GeneralPaperEqualBooleanCallerLifetime.all_phases model W A exponent values v hv small budget phase).trans (le_max_right _ _)

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A exponent c width values budget) := by
  have hEarlier := GeneralPaperEqualPowerWidthCapacity.combined_scale model W exponent c values budget
  have hBoolean := native_scale model W exponent c width values budget
  unfold profile
  fun_prop

def reference {n : ℕ} (model : RationalCostModel) (W exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (profile model W 1 exponent c width values budget)

theorem capacity {n : ℕ} (model : RationalCostModel) (W exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W exponent c width values budget
    profile model W A exponent c width values budget < 2 ^ A :=
  GeneralPaperReferenceCapacity.profile_capacity (fun A => profile model W A exponent c width values budget)
    (combined_scale model W exponent c width values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) :
    let c := count (lottery (rounded true model W exponent values v hv) small)
    let width := (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits
    let A := reference model W exponent c width values budget
    window true model W A exponent values v hv small budget phase < 2 ^ A := by
  let c := count (lottery (rounded true model W exponent values v hv) small)
  let width := (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits
  let A := reference model W exponent c width values budget
  exact (all_phases model W A exponent values v hv small budget phase).trans_lt (capacity model W exponent c width values budget)

end Blotto.GeneralPaperEqualBooleanCapacity
