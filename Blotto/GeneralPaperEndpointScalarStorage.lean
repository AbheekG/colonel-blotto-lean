import Blotto.GeneralPaperSourceFinalEndpointReturnReachedRates

/-! Native outer endpoint scalar ownership, guard comparison, raw copies
and reached reciprocal. All original inputs/results and every scalar-price
prefix are counted. The scratch sum comprises only six constant-count
primitive calls, never initializer, basis or traversal work. This erased
window conservatively reserves the reached scalar branch even at rejection. -/
namespace Blotto.GeneralPaperEndpointScalarStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
open GeneralPaperRetainedBasisEndpoint (numerator denominator)
open GeneralPaperRetainedBasisEndpointBits (guardPrice endpointPrice)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def copied (model : RationalCostModel) (value : ℚ) (reciprocal : Bool) : ℕ :=
  if reciprocal then GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x/y) 1 value
    else model.rat (rationalWordWidth value)
def controls (model : RationalCostModel) (W : ℕ) (endpoint : Farey.Fraction) (value : ℚ) (reciprocal : Bool) : List ℕ :=
  let a := model.rat (1+binaryWordWidth endpoint.num)
  let b := model.rat (1+binaryWordWidth endpoint.den)
  let c := model.rat (GeneralPaperIntegerPrimitivePrice.word (numerator endpoint reciprocal))
  let d := model.rat (1+binaryWordWidth (denominator endpoint reciprocal))
  let e := copied model value reciprocal
  [guardPrice model W value,endpointPrice model W endpoint value reciprocal,a,b,c,d,e,
    a+b,a+b+c,a+b+c+d,a+b+c+d+e,32*W,
    GeneralPaperFinalStaticLoopStorage.bit reciprocal,GeneralPaperFinalStaticLoopStorage.bit (decide (value=0)),
    GeneralPaperFinalStaticLoopStorage.bit (decide (reciprocal=true ∧ value=0))]
def window (model : RationalCostModel) (W : ℕ) (endpoint : Farey.Fraction) (value : ℚ) (reciprocal : Bool) : ℕ :=
  natBits endpoint.num+natBits endpoint.den+integerBits (numerator endpoint reciprocal)+natBits (denominator endpoint reciprocal)+
    rationalWordWidth value+rationalWordWidth (0:ℚ)+rationalWordWidth (1:ℚ)+rationalWordWidth (if reciprocal then 1/value else value)+
    guardPrice model W value+endpointPrice model W endpoint value reciprocal+
    fields W (controls model W endpoint value reciprocal)+128*W
def metadataCap (model : RationalCostModel) (W R : ℕ) : ℕ := 7*model.rat R+64*W+1
def profile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  8*R+7*model.rat R+15*(natBits (metadataCap model W R)+W)+224*W

theorem controls_length (model : RationalCostModel) (W : ℕ) (endpoint : Farey.Fraction) (value : ℚ) (reciprocal : Bool) :
    (controls model W endpoint value reciprocal).length=15 := rfl

theorem bounded (model : RationalCostModel) (W B R : ℕ) (endpoint : Farey.Fraction) (value : ℚ)
    (hNum : endpoint.num≤B) (hDen : endpoint.den≤B) (hValue : RationalHeight value (binaryWordWidth B))
    (hR : GeneralPaperRetainedEndpointBitBounds.priceWidth B≤R) (reciprocal : Bool) :
    window model W endpoint value reciprocal≤profile model W R := by
  have hSmall : 1+binaryWordWidth B≤R := by unfold GeneralPaperRetainedEndpointBitBounds.priceWidth at hR; omega
  have hNumW : natBits endpoint.num≤R := (Nat.add_le_add_left (binaryWordWidth_mono hNum) 1).trans hSmall
  have hDenW : natBits endpoint.den≤R := (Nat.add_le_add_left (binaryWordWidth_mono hDen) 1).trans hSmall
  have hTop : (numerator endpoint reciprocal).natAbs≤B := by cases reciprocal <;> exact (by first | exact hNum | exact hDen)
  have hBottom : denominator endpoint reciprocal≤B := by cases reciprocal <;> exact (by first | exact hDen | exact hNum)
  have hTopW : integerBits (numerator endpoint reciprocal)≤R := (Nat.add_le_add_left (binaryWordWidth_mono hTop) 1).trans hSmall
  have hBottomW : natBits (denominator endpoint reciprocal)≤R := (Nat.add_le_add_left (binaryWordWidth_mono hBottom) 1).trans hSmall
  have hV : rationalWordWidth value≤R := by
    have h := rationalWordWidth_of_height hValue
    unfold GeneralPaperRetainedEndpointBitBounds.priceWidth at hR
    omega
  have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
  have hOneW : rationalWordWidth (1:ℚ)≤R := by
    have h := rationalWordWidth_of_height hOne
    have hp := binaryWordWidth_pos B
    unfold GeneralPaperRetainedEndpointBitBounds.priceWidth at hR
    omega
  have hZeroW : rationalWordWidth (0:ℚ)≤R := by
    have h := rationalWordWidth_of_height (GeneralPaperQuantizedHeight.zero_height (binaryWordWidth B) (binaryWordWidth_pos B))
    unfold GeneralPaperRetainedEndpointBitBounds.priceWidth at hR
    omega
  have hGamma : rationalWordWidth (if reciprocal then 1/value else value)≤R := by
    split
    · have h := rationalWordWidth_of_height (hOne.div hValue)
      unfold GeneralPaperRetainedEndpointBitBounds.priceWidth at hR
      omega
    · exact hV
  have hG := (GeneralPaperRetainedEndpointBitBounds.guard_price model W B value hValue).trans
    (Nat.add_le_add_right (model.monotone hR) _)
  have hE := (GeneralPaperRetainedEndpointBitBounds.endpoint_price model W B endpoint value hNum hDen hValue reciprocal).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 6 (model.monotone hR)) _)
  have hPrefix : model.rat (1+binaryWordWidth endpoint.num)+model.rat (1+binaryWordWidth endpoint.den)+
      model.rat (GeneralPaperIntegerPrimitivePrice.word (numerator endpoint reciprocal))+
      model.rat (1+binaryWordWidth (denominator endpoint reciprocal))+copied model value reciprocal+32*W≤6*model.rat R+32*W := hE
  have hReciprocal := GeneralPaperFinalStaticLoopStorage.bit_bound reciprocal
  have hZero := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (value=0))
  have hGuard := GeneralPaperFinalStaticLoopStorage.bit_bound (decide (reciprocal=true ∧ value=0))
  have hf := fields_bound W (natBits (metadataCap model W R)) (controls model W endpoint value reciprocal) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  rw [controls_length] at hf
  unfold window profile
  omega

end Blotto.GeneralPaperEndpointScalarStorage
