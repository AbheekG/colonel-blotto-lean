import Blotto.GeneralPaperEqualFirstRouteCallerLifetime

/-! One uniform actual source-space observer: first rounding, retained
lengths, packing and all route-table cursors. Shared caller owners are
retained at transitions. Every phase has quasilinear working bits in original
input/budget precision and field count; no space or branch oracle is supplied. -/
namespace Blotto.GeneralPaperEqualFirstSourceSpace
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal)
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth
open GeneralPaperEqualRateAlgebra GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def Phase (n m : ℕ) := Sum (GeneralPaperEqualFirstInitialPrefixLifetime.Phase n)
  (Option (GeneralPaperRouteConstructionLifetime.Phase n m))

def window {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    Phase n (terminal (rounded true model W k values v hv) small).groups.length → ℕ
  | .inl phase => GeneralPaperEqualFirstInitialPrefixLifetime.window model W A k values budget phase
  | .inr none => GeneralPaperEqualFirstPackingCallerLifetime.window model W A k values v hv small budget
  | .inr (some phase) => GeneralPaperEqualFirstRouteCallerLifetime.window model W A k values v hv small budget phase

def profile {n : ℕ} (model : RationalCostModel) (W A k m : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  max (GeneralPaperEqualFirstInitialPrefixLifetime.profile model W A k values budget)
    (max (GeneralPaperEqualFirstPackingCallerLifetime.profile model W A k values budget)
      (GeneralPaperEqualFirstRouteCallerLifetime.profile model W A k m values budget))

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : Phase n (terminal (rounded true model W k values v hv) small).groups.length) :
    window model W A k values v hv small budget phase ≤
      profile model W A k (terminal (rounded true model W k values v hv) small).groups.length values budget := by
  cases phase with
  | inl phase =>
    exact (GeneralPaperEqualFirstInitialPrefixLifetime.all_phases model W A k values v hv budget phase).trans (le_max_left _ _)
  | inr phase =>
    cases phase with
    | none =>
      exact (GeneralPaperEqualFirstPackingCallerLifetime.actual model W A k values v hv small budget).trans
        ((le_max_left _ _).trans (le_max_right _ _))
    | some phase =>
      exact (GeneralPaperEqualFirstRouteCallerLifetime.all_phases model W A k values v hv small budget phase).trans
        ((le_max_right _ _).trans (le_max_right _ _))

theorem packing_scale {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualFirstPackingCallerLifetime.profile model W A k values budget) := by
  apply GeneralPaperEqualPackingCapacity.kernel_scale
  · unfold GeneralPaperEqualFirstPrefixRates.packingBound GeneralPaperEqualPackingExecution.unit
    fun_prop
  · exact GeneralPaperEqualFirstPrefixSpace.profile_scale model W k values budget
  · exact GeneralPaperEqualPackingCapacity.packed_owner_scale n 3 (binaryWordWidth n+k+10)

theorem route_scale {n : ℕ} (model : RationalCostModel) (W k m : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => GeneralPaperEqualFirstRouteCallerLifetime.profile model W A k m values budget) := by
  apply GeneralPaperEqualPreparationLifetime.kernel_scale
  · unfold GeneralPaperEqualFirstPrefixRates.routeBound
    fun_prop
  · exact packing_scale model W k values budget
  · exact GeneralPaperEqualPreparationLifetime.returned_route_scale n 3 (binaryWordWidth n+k+10)

theorem profile_scale {n : ℕ} (model : RationalCostModel) (W k m : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A k m values budget) := by
  have h0 := GeneralPaperEqualFirstPrefixSpace.profile_scale model W k values budget
  have h1 := packing_scale model W k values budget
  have h2 := route_scale model W k m values budget
  unfold profile
  fun_prop

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n m : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ) (budget : Input → ℚ)
    (hW : Tight W) (hA : Tight A) (hn : Small n) (hm : Polylog m)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    Linear (fun x => profile model (W x) (A x) x.k (m x) (values x) (budget x))
      (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+rationalWordWidth (budget x)+n x) := by
  let r := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+rationalWordWidth (budget x)+n x
  have hnRate : Linear n r := bounded 1 (fun x => by dsimp [r]; omega)
  have hw := of_tight hW
  have ha := of_tight hA
  have hmSmall := poly_small hm
  have hWPoly : Polylog W := poly_tight W hW
  have hAPoly : Polylog A := poly_tight A hA
  have hKPoly : Polylog Input.k := poly_tight Input.k k_tight
  have hPrefix := GeneralPaperEqualFirstPrefixSpace.profile_rate model hFast W A n values budget hW hA hn hS
  change Linear _ r at hPrefix ⊢
  dsimp only [profile, GeneralPaperEqualFirstPackingCallerLifetime.profile,
    GeneralPaperEqualFirstRouteCallerLifetime.profile,
    GeneralPaperPackingLifetime.profile, GeneralPaperPackingFrameLifetime.frameProfile,
    GeneralPaperPackingAllocationLifetime.poolProfile, GeneralPaperPackingAllocationLifetime.indicesProfile,
    GeneralPaperRouteConstructionLifetime.profile, GeneralPaperRouteConstructionLifetime.controlProfile,
    GeneralPaperRouteTableLifetime.profile, GeneralPaperRouteGroupFrames.profile,
    GeneralPaperRouteGroupFrames.frameProfile, GeneralPaperRouteMemberFrames.frameProfile,
    GeneralPaperEqualFirstPrefixRates.packingBound, GeneralPaperEqualFirstPrefixRates.routeBound,
    GeneralPaperEqualPackingExecution.unit, GeneralPaperEqualPackedOwner.profile,
    GeneralPaperEqualRouteOwner.profile, GeneralPaperEncodedBasisStorage.arrayProfile,
    GeneralPaperPositiveScanLifetime.labelProfile, GeneralPaperIndexedArrayLifetime.frame,
    GeneralPaperEqualRouteConstruction.indicesWork]
  fun_prop (config := {maxSteps := 30000})

theorem every_phase_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j, (values x).read j = (v x).weight j)
    (small : ∀ x j, 2*(rounded true model (W x) x.k (values x) (v x) (hv x)).weight j ≤ 1)
    (budget : Input → ℚ) (hW : Tight W) (hA : Tight A) (hn : Small n)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    ∃ C d : ℕ, ∀ x (phase : Phase (n x)
        (terminal (rounded true model (W x) x.k (values x) (v x) (hv x)) (small x)).groups.length),
      window model (W x) (A x) x.k (values x) (v x) (hv x) (small x) (budget x) phase ≤
        C*(GeneralPaperValueRoundingInputPrice.inputSize (values x)+rationalWordWidth (budget x)+n x+1)*(logSize x)^d := by
  let m := fun x => (terminal (rounded true model (W x) x.k (values x) (v x) (hv x)) (small x)).groups.length
  have hm : Polylog m := by
    apply GeneralPaperSourceSoftBounds.bounded (r := fun _ => 1) 3
    intro x
    simpa only [Nat.mul_one] using (GeneralPaperEqualFirstNativeCache.group_count
      (rounded true model (W x) x.k (values x) (v x) (hv x)) (small x))
  obtain ⟨C,d,h⟩ := profile_rate model hFast W A n m values budget hW hA hn hm hS
  exact ⟨C,d,fun x phase => (all_phases model (W x) (A x) x.k (values x) (v x) (hv x) (small x) (budget x) phase).trans (h x)⟩

end Blotto.GeneralPaperEqualFirstSourceSpace
