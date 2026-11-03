import Blotto.GeneralPaperNatPowerBitConstructionStorage

/-! Actual scale construction and the complete scale/round/sum caller.
Repeated squaring, both natural products, their scratch and all parent work
fields are included while the original rational array remains retained. -/
namespace Blotto.GeneralPaperNativeScaleConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W c n k : ℕ) : ℕ := GeneralPaperOriginalSourceValuePrice.scalePrice model W c n k
def cap (model : RationalCostModel) (W c n k : ℕ) : ℕ := c+n+k+2^k+c*n+c*n*2^k+price model W c n k+128*W+1

def controls (model : RationalCostModel) (W c n k : ℕ) : List ℕ :=
  let power := GeneralPaperNatPowerBits.run model.rat W 2 k
  let first := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c n
  let second := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) (c*n) power.1.power
  let made := GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k
  [c,n,k,power.1.power,c*n,made.1,power.2,first,second,128*W,power.2+first,power.2+first+second,made.2]

def window (model : RationalCostModel) (W c n k : ℕ) : ℕ :=
  let power := GeneralPaperNatPowerBits.run model.rat W 2 k
  GeneralPaperNatPowerBitConstructionStorage.window model W 2 k+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c n+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) (c*n) power.1.power+
    fields W (controls model W c n k)+128*W

def profile (model : RationalCostModel) (W c n k : ℕ) : ℕ :=
  GeneralPaperNatPowerBitConstructionStorage.profile model W 2 k+
    price model W c n k+13*(natBits (cap model W c n k)+W)+160*W

theorem work (model : RationalCostModel) (W c n k : ℕ) :
    (GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).2≤price model W c n k :=
  (GeneralPaperValueRoundingPaperContract.scale_bit_work model W c n k).trans
    (GeneralPaperOriginalSourceValuePrice.scale_price model W c n n k le_rfl)

theorem bounded (model : RationalCostModel) (W c n k : ℕ) : window model W c n k≤profile model W c n k := by
  let power := GeneralPaperNatPowerBits.run model.rat W 2 k
  let first := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c n
  let second := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) (c*n) power.1.power
  have hPower := GeneralPaperNatPowerBitConstructionStorage.bounded model W 2 k k (by decide) le_rfl
  have hw := work model W c n k
  have hShape : (GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).2=power.2+first+second+128*W := rfl
  have hPow : power.1.power=2^k := by rw [GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data 2 k).1]
  have hValue : (GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).1=c*n*2^k :=
    GeneralPaperValueRoundingPaperContract.scale_data true model W c n k
  have hf := fields_bound W (natBits (cap model W c n k)) (controls model W c n k) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    change z=c ∨ z=n ∨ z=k ∨ z=power.1.power ∨ z=c*n ∨ z=(GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).1 ∨
      z=power.2 ∨ z=first ∨ z=second ∨ z=128*W ∨ z=power.2+first ∨ z=power.2+first+second ∨
      z=(GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).2 at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤13*(natBits (cap model W c n k)+W)+32*W at hf
  change GeneralPaperNatPowerBitConstructionStorage.window model W 2 k+first+second+fields W (controls model W c n k)+128*W≤_
  unfold profile
  omega

def roundingPrice (model : RationalCostModel) (W c n k S : ℕ) : ℕ :=
  price model W c n k+GeneralPaperValueWeightSumConstructionStorage.driverPrice model W n
    (GeneralPaperValueRoundingPaperContract.scale c n k) S+128*W
def roundingCap (model : RationalCostModel) (W c n k S : ℕ) : ℕ :=
  c+n+k+GeneralPaperValueRoundingPaperContract.scale c n k+roundingPrice model W c n k S+128*W+1

def roundingControls {n : ℕ} (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ) : List ℕ :=
  let scale := GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k
  let rounded := GeneralPaperValueRoundingDriver.run true model W scale.1 values
  let made := GeneralPaperValueRoundingPaperContract.run true model W c k values
  [c,n,k,scale.1,scale.2,rounded.2,128*W,scale.2+rounded.2,made.2]

def roundingWindow {n : ℕ} (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  let scale := GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k
  arrayFootprint W rationalWordWidth values+window model W c n k+
    GeneralPaperValueWeightSumConstructionStorage.driverWindow model W scale.1 values count hc+
    fields W (roundingControls model W c k values)+128*W

def roundingProfile (model : RationalCostModel) (W c n k S : ℕ) : ℕ :=
  S+n*W+64*W+profile model W c n k+
    GeneralPaperValueWeightSumConstructionStorage.driverProfile model W n (GeneralPaperValueRoundingPaperContract.scale c n k) S+
    9*(natBits (roundingCap model W c n k S)+W)+160*W

theorem rounding_work {n : ℕ} (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperValueRoundingPaperContract.run true model W c k values).2≤roundingPrice model W c n k (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have hs := work model W c n k
  have hr := GeneralPaperValueWeightSumConstructionStorage.driver_work model W
    (GeneralPaperValueRoundingPaperContract.scale c n k) values v hv
  unfold GeneralPaperValueRoundingPaperContract.run roundingPrice
  dsimp only
  rw [GeneralPaperValueRoundingPaperContract.scale_data]
  omega

theorem rounding_bounded {n : ℕ} (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (count : ℕ) (hc : count≤n) :
    roundingWindow model W c k values count hc≤roundingProfile model W c n k (GeneralPaperValueRoundingInputPrice.inputSize values) := by
  have hScale := bounded model W c n k
  have hRound := GeneralPaperValueWeightSumConstructionStorage.driver_bounded model W
    (GeneralPaperValueRoundingPaperContract.scale c n k) values v hv count hc
  have hInput : arrayFootprint W rationalWordWidth values=GeneralPaperValueRoundingInputPrice.inputSize values+n*W+64*W := by
    unfold arrayFootprint GeneralPaperValueRoundingInputPrice.inputSize
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    omega
  have hw := rounding_work model W c k values v hv
  have hShape : (GeneralPaperValueRoundingPaperContract.run true model W c k values).2=
      (GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).2+
      (GeneralPaperValueRoundingDriver.run true model W (GeneralPaperValueRoundingPaperContract.scaleRun true model W c n k).1 values).2+128*W := rfl
  have hValue := GeneralPaperValueRoundingPaperContract.scale_data true model W c n k
  have hf := fields_bound W (natBits (roundingCap model W c n k (GeneralPaperValueRoundingInputPrice.inputSize values)))
    (roundingControls model W c k values) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [roundingControls,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold roundingCap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤9*(natBits (roundingCap model W c n k (GeneralPaperValueRoundingInputPrice.inputSize values))+W)+32*W at hf
  unfold roundingWindow roundingProfile
  dsimp only
  rw [GeneralPaperValueRoundingPaperContract.scale_data]
  omega

@[fun_prop]
theorem scaling (model : RationalCostModel) (c n k : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile model W c n k) := by
  unfold profile cap price GeneralPaperOriginalSourceValuePrice.scalePrice
  fun_prop

@[fun_prop]
theorem rounding_scaling (model : RationalCostModel) (c n k S : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => roundingProfile model W c n k S) := by
  unfold roundingProfile roundingCap roundingPrice price GeneralPaperOriginalSourceValuePrice.scalePrice
    GeneralPaperValueWeightSumConstructionStorage.driverPrice GeneralPaperValueWeightSumConstructionStorage.price
    GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice
    GeneralPaperNativePayloadFillStorage.workCap GeneralPaperSummaryArrayExecution.arrayWord
  dsimp only
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds

theorem price_poly {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W c n : Input → ℕ) (hW : Tight W) (hc : Small c) (hn : Small n) :
    Polylog (fun x => price model (W x) (c x) (n x) x.k) := by
  have hr : Polylog W := poly_tight W hW
  have hPowerOperand : Polylog (fun x => GeneralPaperNatPowerOperands.width 2 x.k) := by
    unfold GeneralPaperNatPowerOperands.width
    fun_prop
  have hScaleOperand : Polylog (fun x => GeneralPaperOriginalSourceValuePrice.scaleWidth (c x) (n x) x.k) := by
    unfold GeneralPaperOriginalSourceValuePrice.scaleWidth
    fun_prop
  have hp : Polylog (fun x => model.rat (GeneralPaperNatPowerOperands.width 2 x.k)) :=
    primitive_preserves hg hPowerOperand (GeneralPaperCacheConstructionGrowth.small_of_poly hPowerOperand)
  have hs : Polylog (fun x => model.rat (GeneralPaperOriginalSourceValuePrice.scaleWidth (c x) (n x) x.k)) :=
    primitive_preserves hg hScaleOperand (GeneralPaperCacheConstructionGrowth.small_of_poly hScaleOperand)
  unfold price GeneralPaperOriginalSourceValuePrice.scalePrice
  fun_prop

theorem profile_poly {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W c n : Input → ℕ) (hW : Tight W) (hc : Small c) (hn : Small n) :
    Polylog (fun x => profile model (W x) (c x) (n x) x.k) := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hPowerSmall : Small (fun x => 2^x.k) := pow_two _ k_tight
  have hPower := GeneralPaperNatPowerBitConstructionStorage.dyadic_profile_poly hg W hW
  have hPrice := price_poly hg W c n hW hc hn
  have hPriceSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hPrice
  unfold profile cap natBits
  fun_prop

theorem rounding_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W c n S : Input → ℕ) (hW : Tight W) (hc : Small c) (hn : Small n) (hS : Small S) :
    Soft (fun x => S x+n x+1) (fun x => roundingProfile model (W x) (c x) (n x) x.k (S x)) := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hPowerSmall : Small (fun x => 2^x.k) := pow_two _ k_tight
  have hM : Small (fun x => GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k) := by
    unfold GeneralPaperValueRoundingPaperContract.scale
    fun_prop
  have hScale := profile_poly hg W c n hW hc hn
  have hPrice := price_poly hg W c n hW hc hn
  have hPriceSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hPrice
  have hRound := GeneralPaperValueWeightSumConstructionStorage.driver_profile_rate hg W n
    (fun x => GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k) S hW hn hM hS
  have hLong : Small (fun x => GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth
      (GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k) (S x)) := by
    unfold GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth
    fun_prop
  have hLongPrice := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hLong
  have hShort : Small (fun x => 1+binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k+n x)) := by fun_prop
  have hShortPrice := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hShort
  have hTail : Polylog (fun x => 64*W x+profile model (W x) (c x) (n x) x.k+
      9*(natBits (roundingCap model (W x) (c x) (n x) x.k (S x))+W x)+160*W x) := by
    unfold roundingCap roundingPrice GeneralPaperValueWeightSumConstructionStorage.driverPrice
      GeneralPaperValueWeightSumConstructionStorage.price GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice
      GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice GeneralPaperNativePayloadFillStorage.workCap
      GeneralPaperSummaryArrayExecution.arrayWord natBits
    dsimp only
    fun_prop (config := {maxSteps := 20000})
  have hInput : Soft (fun x => S x+n x+1) S := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by omega)
  have hN : Soft (fun x => S x+n x+1) n := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by omega)
  have hTail' := poly_at_rate hTail (fun x => by omega : ∀ x,1≤S x+n x+1)
  apply GeneralPaperSourceSoftBounds.dominated (add_same (add_same (add_same hInput (mul_poly hN hr)) hRound) hTail')
  intro x
  unfold roundingProfile
  omega

end Blotto.GeneralPaperNativeScaleConstructionStorage
