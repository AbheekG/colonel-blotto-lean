import Blotto.GeneralPaperEqualInitialPrefixLifetime

/-! Common analysis capacity for native rounding/length phases and the
already proved segment-through-return phases. Packing/route construction
is absent; the program-computed whole common reference is still open. -/
namespace Blotto.GeneralPaperEqualInitialPrefixCapacity
open GeneralPaperReferenceScaling
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

theorem input_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualInitialPrefixLifetime.inputProfile model W A exponent values budget) := by
  unfold GeneralPaperEqualInitialPrefixLifetime.inputProfile
  fun_prop

theorem rounded_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualInitialPrefixLifetime.roundedProfile model W A exponent values budget) := by
  have hInput := input_scale model W exponent values budget
  unfold GeneralPaperEqualInitialPrefixLifetime.roundedProfile
  fun_prop

theorem prefix_scale {n : ℕ} (model : RationalCostModel) (W exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualInitialPrefixLifetime.profile model W A exponent values budget) := by
  have hInput := input_scale model W exponent values budget
  have hRounded := rounded_scale model W exponent values budget
  have hLength := GeneralPaperEqualLengthReferenceScaling.profile_scale model n (binaryWordWidth n + exponent + 11) _ hRounded
  have hReturn := GeneralPaperEqualLengthReturnStorage.profile_scale model n (binaryWordWidth n + exponent + 11) _ hRounded
  unfold GeneralPaperEqualInitialPrefixLifetime.profile
  fun_prop

def Phase (n m c K width : ℕ) := Sum (GeneralPaperEqualInitialPrefixLifetime.Phase n) (GeneralPaperEqualFinalClosureCapacity.Phase m c K width)

def window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase n (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits → ℕ
  | .inl phase => GeneralPaperEqualInitialPrefixLifetime.window model W A exponent values budget phase
  | .inr phase => GeneralPaperEqualFinalClosureCapacity.window true model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualInitialPrefixLifetime.profile model W A exponent values budget)
    (GeneralPaperEqualFinalClosureCapacity.profile model W A exponent m c width values budget)

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
  | inl phase =>
    exact (GeneralPaperEqualInitialPrefixLifetime.all_phases model W A exponent values v hv budget phase).trans (le_max_left _ _)
  | inr phase =>
    exact (GeneralPaperEqualFinalClosureCapacity.all_phases model W A exponent values v hv small budget phase).trans (le_max_right _ _)

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A exponent m c width values budget) := by
  have hPrefix := prefix_scale model W exponent values budget
  have hTail := GeneralPaperEqualFinalClosureCapacity.combined_scale model W exponent m c width values budget
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

end Blotto.GeneralPaperEqualInitialPrefixCapacity
