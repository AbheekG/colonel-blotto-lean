import Blotto.GeneralPaperEqualRouteCallerLifetime

/-! Every native bit-preparation phase now has one conservative reserve.
The returned initial-prefix owner is also retained uniformly, preserving
arrays allocated at the original input-reference width in later phases.
Capacity here is analysis-only at fixed W; construction of one common
preparation/draw word and sharp paper rates remain separate obligations. -/
namespace Blotto.GeneralPaperEqualPreparationLifetime
open GeneralPaperReferenceScaling
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

@[fun_prop]
theorem table_scale (n m s : ℕ) :
    Scale (fun A => GeneralPaperRouteTableLifetime.profile A n m s) := by
  unfold GeneralPaperRouteTableLifetime.profile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem returned_route_scale (n m s : ℕ) :
    Scale (fun A => GeneralPaperEqualRouteOwner.profile A n m s) := by
  unfold GeneralPaperEqualRouteOwner.profile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem controls_scale (n m F : ℕ) :
    Scale (fun A => GeneralPaperRouteConstructionLifetime.controlProfile A n m F) := by
  unfold GeneralPaperRouteConstructionLifetime.controlProfile
  fun_prop

@[fun_prop]
theorem member_frame_scale (n m : ℕ) (F : ℕ → ℕ) (hf : Scale F) :
    Scale (fun A => GeneralPaperRouteMemberFrames.frameProfile A n m (F A)) := by
  unfold GeneralPaperRouteMemberFrames.frameProfile
  fun_prop

@[fun_prop]
theorem group_frame_scale (n m s : ℕ) (F : ℕ → ℕ) (hf : Scale F) :
    Scale (fun A => GeneralPaperRouteGroupFrames.frameProfile A n m (F A) s) := by
  unfold GeneralPaperRouteGroupFrames.frameProfile
  fun_prop

@[fun_prop]
theorem group_scale (n m s : ℕ) (F : ℕ → ℕ) (hf : Scale F) :
    Scale (fun A => GeneralPaperRouteGroupFrames.profile A n m (F A) s) := by
  unfold GeneralPaperRouteGroupFrames.profile
  fun_prop

@[fun_prop]
theorem variable_controls_scale (n m : ℕ) (F : ℕ → ℕ) (hf : Scale F) :
    Scale (fun A => GeneralPaperRouteConstructionLifetime.controlProfile A n m (F A)) := by
  unfold GeneralPaperRouteConstructionLifetime.controlProfile
  fun_prop

theorem kernel_scale (n m s : ℕ) (F borrowed returned : ℕ → ℕ) (hF : Scale F) (hB : Scale borrowed) (hR : Scale returned) :
    Scale (fun A => GeneralPaperRouteConstructionLifetime.profile A n m (F A) s (borrowed A) (returned A)) := by
  unfold GeneralPaperRouteConstructionLifetime.profile
  fun_prop

theorem native_scale {n : ℕ} (model : RationalCostModel) (W exponent m : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualRouteCallerLifetime.profile model W A exponent m values budget) :=
  kernel_scale n m (binaryWordWidth n + exponent + 9) _ _ _
    (GeneralPaperEqualSegmentCallerCapacity.ledger_scale model W exponent values (rationalWordWidth budget))
    (GeneralPaperEqualPackingCapacity.native_scale model W exponent values budget)
    (returned_route_scale n 3 (binaryWordWidth n + exponent + 9))

def Phase (n m c K width : ℕ) := Sum (GeneralPaperEqualPackingCapacity.Phase n m c K width) (GeneralPaperRouteConstructionLifetime.Phase n m)

def retainedPrefix {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualInitialPrefixLifetime.window model W A exponent values budget .returned

def window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase n (terminal (rounded true model W exponent values v hv) small).groups.length
      (count (lottery (rounded true model W exponent values v hv) small)) (exponent + 5)
      (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits) : ℕ :=
  retainedPrefix model W A exponent values budget +
    match phase with
    | .inl phase => GeneralPaperEqualPackingCapacity.window model W A exponent values v hv small budget phase
    | .inr phase => GeneralPaperEqualRouteCallerLifetime.window model W A exponent values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualInitialPrefixLifetime.profile model W A exponent values budget +
    max (GeneralPaperEqualPackingCapacity.profile model W A exponent m c width values budget)
      (GeneralPaperEqualRouteCallerLifetime.profile model W A exponent m values budget)

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
  have hPrefix := GeneralPaperEqualInitialPrefixLifetime.all_phases model W A exponent values v hv budget .returned
  cases phase with
  | inl phase =>
    exact Nat.add_le_add hPrefix ((GeneralPaperEqualPackingCapacity.all_phases model W A exponent values v hv small budget phase).trans (le_max_left _ _))
  | inr phase =>
    exact Nat.add_le_add hPrefix ((GeneralPaperEqualRouteCallerLifetime.all_phases model W A exponent values v hv small budget phase).trans (le_max_right _ _))

theorem combined_scale {n : ℕ} (model : RationalCostModel) (W exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A exponent m c width values budget) := by
  have hPrefix := GeneralPaperEqualInitialPrefixCapacity.prefix_scale model W exponent values budget
  have hEarlier := GeneralPaperEqualPackingCapacity.combined_scale model W exponent m c width values budget
  have hRoutes := native_scale model W exponent m values budget
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

end Blotto.GeneralPaperEqualPreparationLifetime
