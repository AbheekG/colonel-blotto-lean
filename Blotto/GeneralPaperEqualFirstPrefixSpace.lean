import Blotto.GeneralPaperEqualFirstNativeCache

/-! Uniform source-prefix capacity and quasilinear working bits for actual
c=256 rounding and length construction. The capacity is derived from the
proved profile; executable full-preparation word calibration remains separate. -/
namespace Blotto.GeneralPaperEqualFirstPrefixSpace
open GeneralPaperReferenceScaling
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth
open GeneralPaperEqualRateAlgebra
open GeneralPaperEqualFirstInitialPrefixLifetime
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem input_scale {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => inputProfile model W A k values budget) := by
  unfold inputProfile
  fun_prop

theorem rounded_scale {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => roundedProfile model W A k values budget) := by
  have h := input_scale model W k values budget
  unfold roundedProfile
  fun_prop

theorem profile_scale {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    Scale (fun A => profile model W A k values budget) := by
  have hInput := input_scale model W k values budget
  have hRounded := rounded_scale model W k values budget
  have hLength := GeneralPaperEqualLengthReferenceScaling.profile_scale model n (binaryWordWidth n+k+12) _ hRounded
  have hReturn := GeneralPaperEqualLengthReturnStorage.profile_scale model n (binaryWordWidth n+k+12) _ hRounded
  unfold profile
  fun_prop

def reference {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (profile model W 1 k values budget)

theorem capacity {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) :
    let A := reference model W k values budget
    profile model W A k values budget < 2^A := by
  change (fun A => profile model W A k values budget)
    (GeneralPaperReferenceCapacity.referenceWord ((fun A => profile model W A k values budget) 1)) < _
  exact GeneralPaperReferenceCapacity.profile_capacity
    (fun A => profile model W A k values budget) (profile_scale model W k values budget)

theorem actual_capacity {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (phase : Phase n) :
    let A := reference model W k values budget
    window model W A k values budget phase < 2^A :=
  (all_phases model W _ k values v hv budget phase).trans_lt (capacity model W k values budget)

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ) (budget : Input → ℚ)
    (hW : Tight W) (hA : Tight A) (hn : Small n)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    Linear (fun x => profile model (W x) (A x) x.k (values x) (budget x))
      (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+rationalWordWidth (budget x)+n x) := by
  let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  let b := fun x => rationalWordWidth (budget x)
  let r := fun x => S x+b x+n x
  have hnRate : Linear n r := bounded 1 (fun x => by dsimp [r]; omega)
  have hSRate : Linear S r := bounded 1 (fun x => by dsimp [r]; omega)
  have hbRate : Linear b r := bounded 1 (fun x => by dsimp [r]; omega)
  have hw := of_tight hW
  have ha := of_tight hA
  have hWPoly : Polylog W := poly_tight W hW
  have hAPoly : Polylog A := poly_tight A hA
  have hKPoly : Polylog Input.k := poly_tight Input.k k_tight
  obtain ⟨C,d,hg⟩ := hFast
  have hFast : GeneralPaperFastRationalModel.IsFast model := ⟨C,d,hg⟩
  have hRound := GeneralPaperNativeScaleConstructionStorage.rounding_profile_rate hg W (fun _ => 256) n S
    hW (small_constant 256) hn hS
  have hRoundRate : Linear (fun x => GeneralPaperNativeScaleConstructionStorage.roundingProfile model
      (W x) 256 (n x) x.k (S x)) r := rate_mono hRound (fun x => by dsimp [r]; omega)
  have hRoundTimeSmall : Small (fun x => GeneralPaperNativeScaleConstructionStorage.roundingPrice model
      (W x) 256 (n x) x.k (S x)) := by
    unfold GeneralPaperNativeScaleConstructionStorage.roundingPrice GeneralPaperNativeScaleConstructionStorage.price
      GeneralPaperOriginalSourceValuePrice.scalePrice GeneralPaperOriginalSourceValuePrice.scaleWidth
      GeneralPaperValueWeightSumConstructionStorage.driverPrice GeneralPaperValueWeightSumConstructionStorage.price
      GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
      GeneralPaperNativePayloadFillStorage.workCap GeneralPaperValueRoundingPaperContract.scale
      GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth GeneralPaperSummaryArrayExecution.arrayWord
      GeneralPaperNatPowerOperands.width
    dsimp only
    fun_prop (config := {maxSteps := 20000})
  dsimp only [S,b] at hSRate hbRate hRoundRate hRoundTimeSmall
  change Linear _ r
  dsimp only [profile, roundedProfile, inputProfile, roundingTime,
    GeneralPaperEqualPrefixOwners.roundedProfile, GeneralPaperSummaryArrayExecution.arrayWord,
    GeneralPaperEqualLengthReturnStorage.profile, GeneralPaperEqualLengthPhaseStorage.profile,
    GeneralPaperEqualLengthPhaseStorage.loopProfile, GeneralPaperIndexedArrayLifetime.frame,
    GeneralPaperEncodedBasisStorage.arrayProfile, GeneralPaperEqualLengthArray.height,
    GeneralPaperEqualDenominatorLifetime.profile, expressionHeightBudget]
  fun_prop (config := {maxSteps := 30000})

theorem every_phase_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (W A n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j, (values x).read j = (v x).weight j)
    (budget : Input → ℚ) (hW : Tight W) (hA : Tight A) (hn : Small n)
    (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    ∃ C d : ℕ, ∀ x (phase : Phase (n x)),
      window model (W x) (A x) x.k (values x) (budget x) phase ≤
        C*(GeneralPaperValueRoundingInputPrice.inputSize (values x)+rationalWordWidth (budget x)+n x+1)*(logSize x)^d := by
  obtain ⟨C,d,h⟩ := profile_rate model hFast W A n values budget hW hA hn hS
  exact ⟨C,d,fun x phase => (all_phases model (W x) (A x) x.k (values x) (v x) (hv x) (budget x) phase).trans (h x)⟩

end Blotto.GeneralPaperEqualFirstPrefixSpace
