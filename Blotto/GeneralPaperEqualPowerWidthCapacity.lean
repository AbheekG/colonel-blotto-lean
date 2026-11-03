import Blotto.GeneralPaperEqualPowerWidthCaller

/-! A common analysis reserve now covers consecutive native segment,
compaction, integer, midpoint-power and rejection-width preparation phases.
This reference is not computed by the program; Boolean/final closure and
initial prefix construction are still outside this partial phase chain. -/
namespace Blotto.GeneralPaperEqualPowerWidthCapacity
open GeneralPaperReferenceScaling
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (lottery terminal)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[fun_prop]
theorem power_price_scale (model : RationalCostModel) (K : ℕ) :
    Scale (fun A => GeneralPaperNatPowerBitConstructionStorage.price model A 2 K) := by
  unfold GeneralPaperNatPowerBitConstructionStorage.price
  fun_prop

@[fun_prop]
theorem cached_power_scale (model : RationalCostModel) (K : ℕ) :
    Scale (fun A => GeneralPaperEqualPowerWidthLifetime.cachedPowerProfile model A K) := by
  unfold GeneralPaperEqualPowerWidthLifetime.cachedPowerProfile
  fun_prop

@[fun_prop]
theorem width_storage_scale (model : RationalCostModel) (R : ℕ) :
    Scale (fun A => GeneralPaperPowerCeilingStorage.profile model A R) := by
  unfold GeneralPaperPowerCeilingStorage.profile GeneralPaperPowerCeilingStorage.frameProfile
    GeneralPaperPowerCeilingStorage.metadataCap GeneralPaperPowerCeilingStorage.price
  fun_prop

@[fun_prop]
theorem width_time_scale (model : RationalCostModel) (L : ℕ) :
    Scale (fun A => GeneralPaperEqualPowerWidthLifetime.widthTime model A L) := by
  unfold GeneralPaperEqualPowerWidthLifetime.widthTime
  fun_prop

@[fun_prop]
theorem control_scale (model : RationalCostModel) (L K : ℕ) :
    Scale (fun A => GeneralPaperEqualPowerWidthLifetime.controlProfile model A L K) := by
  unfold GeneralPaperEqualPowerWidthLifetime.controlProfile GeneralPaperEqualPowerWidthLifetime.controlCap
  fun_prop

theorem kernel_scale (model : RationalCostModel) (L K : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperEqualPowerWidthLifetime.profile model A L K (borrowed A)) := by
  unfold GeneralPaperEqualPowerWidthLifetime.profile
  fun_prop

theorem native_scale {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualPowerWidthCaller.profile model W A exponent c values budget) :=
  kernel_scale model _ _ _ (GeneralPaperEqualIntegerCallerCapacity.profile_scale model W exponent c values budget)

def Phase (m c K : ℕ) := Sum (GeneralPaperEqualMiddlePreparationLifetime.Phase m c) (GeneralPaperEqualPowerWidthLifetime.Phase K)

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase (terminal (rounded bits model W exponent values v hv) small).groups.length
      (count (lottery (rounded bits model W exponent values v hv) small)) (exponent + 5) → ℕ
  | .inl phase => GeneralPaperEqualMiddlePreparationLifetime.window bits model W A exponent values v hv small budget phase
  | .inr phase => GeneralPaperEqualPowerWidthCaller.window bits model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualMiddlePreparationLifetime.profile model W A exponent c values budget)
    (GeneralPaperEqualPowerWidthCaller.profile model W A exponent c values budget)

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (count (lottery (rounded true model W exponent values v hv) small)) values budget := by
  cases phase with
  | inl phase =>
    exact (GeneralPaperEqualMiddlePreparationLifetime.all_phases model W A exponent values v hv small budget phase).trans
      (le_max_left _ _)
  | inr phase =>
    exact (GeneralPaperEqualPowerWidthCaller.all_phases model W A exponent values v hv small budget phase).trans
      (le_max_right _ _)

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A exponent c values budget) := by
  have hEarlier := GeneralPaperEqualCompactionCapacity.combined_scale model W exponent c values budget
  have hPowerWidth := native_scale model W exponent c values budget
  unfold profile
  fun_prop

def reference {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (profile model W 1 exponent c values budget)

theorem capacity {n : ℕ} (model : RationalCostModel) (W exponent c : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W exponent c values budget
    profile model W A exponent c values budget < 2 ^ A :=
  GeneralPaperReferenceCapacity.profile_capacity (fun A => profile model W A exponent c values budget)
    (combined_scale model W exponent c values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)) :
    let c := count (lottery (rounded true model W exponent values v hv) small)
    let A := reference model W exponent c values budget
    window true model W A exponent values v hv small budget phase < 2 ^ A := by
  let c := count (lottery (rounded true model W exponent values v hv) small)
  let A := reference model W exponent c values budget
  exact (all_phases model W A exponent values v hv small budget phase).trans_lt (capacity model W exponent c values budget)

end Blotto.GeneralPaperEqualPowerWidthCapacity
