import Blotto.GeneralPaperDescriptionHeadline

/-! Literal shared coefficient construction. Input weights, full output,
fill buffers/frames, rational cast/division and natural-product scratch,
and all scalar/native work fields coexist in the declared paper model. -/
namespace Blotto.GeneralPaperCircleCoefficientConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperCircleRationalCoefficients
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def callbackPrice (model : RationalCostModel) (W R mass : ℕ) : ℕ := 5*model.rat (width R mass)+64*W
def scalarCap (model : RationalCostModel) (W R mass : ℕ) : ℕ := R+mass+R*mass+callbackPrice model W R mass+1

def scalarControls (model : RationalCostModel) (W R mass w : ℕ) : List ℕ :=
  let product := R*w
  let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R w
  let cast := model.rat (rationalWordWidth (product:ℚ))
  let divide := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) product mass
  [R,w,product,multiply,cast,divide,multiply+cast,multiply+cast+divide,64*W,
    (coordinate model.rat W R mass w).2]

def scalarWindow (model : RationalCostModel) (W R mass w : ℕ) : ℕ :=
  let product := R*w
  rationalWordWidth (mass:ℚ)+rationalWordWidth (product:ℚ)+rationalWordWidth ((product:ℚ)/mass)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R w+
    model.rat (rationalWordWidth (product:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) product mass+
    fields W (scalarControls model W R mass w)+128*W

def scalarProfile (model : RationalCostModel) (W R mass : ℕ) : ℕ :=
  3*width R mass+5*model.rat (width R mass)+10*(natBits (scalarCap model W R mass)+W)+160*W

theorem scalar_bound (model : RationalCostModel) (W R mass w : ℕ) (hw : w≤mass) :
    scalarWindow model W R mass w≤scalarProfile model W R mass := by
  let product := R*w
  let multiply := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R w
  let cast := model.rat (rationalWordWidth (product:ℚ))
  let divide := GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) product mass
  have hProduct := product_width R mass w hw
  change rationalWordWidth (product:ℚ)≤width R mass at hProduct
  have hMass := denominator_width R mass
  have hRatio := ratio_width R mass w hw
  change rationalWordWidth ((product:ℚ)/mass)≤width R mass at hRatio
  have hMul := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) R w (width R mass)
    (by unfold width;omega) (by have h := binaryWordWidth_mono hw;unfold width;omega)
    (by have h := binaryWordWidth_mul R w;have h' := binaryWordWidth_mono hw;unfold width;omega)
  change multiply≤2*model.rat (width R mass) at hMul
  have hCast : cast≤model.rat (width R mass) := model.monotone hProduct
  have hDiv : divide≤2*model.rat (width R mass) :=
    GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) product mass _ hProduct hMass hRatio
  have hWork := coordinate_work model.rat model.monotone W R mass w hw
  change (coordinate model.rat W R mass w).2≤callbackPrice model W R mass at hWork
  have hShape : (coordinate model.rat W R mass w).2=multiply+cast+divide+64*W := rfl
  have hProductN : product≤R*mass := Nat.mul_le_mul_left R hw
  have hf := fields_bound W (natBits (scalarCap model W R mass)) (scalarControls model W R mass w) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    dsimp only [scalarControls] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    change z=R ∨ z=w ∨ z=product ∨ z=multiply ∨ z=cast ∨ z=divide ∨ z=multiply+cast ∨
      z=multiply+cast+divide ∨ z=64*W ∨ z=(coordinate model.rat W R mass w).2 at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold scalarCap;omega)
  change fields W _≤10*(natBits (scalarCap model W R mass)+W)+32*W at hf
  change rationalWordWidth (mass:ℚ)+rationalWordWidth (product:ℚ)+rationalWordWidth ((product:ℚ)/mass)+
    multiply+cast+divide+fields W (scalarControls model W R mass w)+128*W≤_
  unfold scalarProfile
  nlinarith only [hProduct,hMass,hRatio,hMul,hCast,hDiv,hf]

def price (model : RationalCostModel) (W g R mass : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W g (callbackPrice model W R mass)+model.rat (width R mass)+16*W
def metadataCap (model : RationalCostModel) (W g R mass : ℕ) : ℕ := g+price model W g R mass+64*W+1

def window {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (count : ℕ) (hc : count≤g) : ℕ :=
  let stored := PaperIndexedArrayConstruction.run (fun w => w) W (fun j => coordinate model.rat W R mass (weights.read j))
  let cast := model.rat (rationalWordWidth (mass:ℚ))
  let result := GeneralPaperCircleRationalCoefficients.run model.rat (fun w => w) W R mass weights
  arrayFootprint W natBits weights+rationalWordWidth (mass:ℚ)+cast+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (fun j => coordinate model.rat W R mass (weights.read j))
      (fun j => scalarWindow model W R mass (weights.read j)) count hc+
    fields W [g,stored.2,cast,16*W,result.2]+128*W

def profile (model : RationalCostModel) (W g R mass : ℕ) : ℕ :=
  arrayProfile W g (natBits mass)+width R mass+model.rat (width R mass)+
    GeneralPaperNativePayloadFillStorage.profile W (width R mass) g (callbackPrice model W R mass) (scalarProfile model W R mass)+
    5*(natBits (metadataCap model W g R mass)+W)+160*W

theorem work {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (hw : ∀ j,weights.read j≤mass) (hW : 1≤W) (hIndex : binaryWordWidth (g+1)≤W) :
    (GeneralPaperCircleRationalCoefficients.run model.rat (fun w => w) W R mass weights).2≤price model W g R mass := by
  have hFill := GeneralPaperNativePayloadFillStorage.prefix_work W (callbackPrice model W R mass)
    (fun j => coordinate model.rat W R mass (weights.read j))
    (fun j => coordinate_work model.rat model.monotone W R mass _ (hw j)) hW hIndex g le_rfl
  change (PaperIndexedArrayConstruction.run (fun w => w) W
    (fun j => coordinate model.rat W R mass (weights.read j))).2≤
      GeneralPaperNativePayloadFillStorage.workCap W g (callbackPrice model W R mass) at hFill
  have hCast := model.monotone (denominator_width R mass)
  unfold GeneralPaperCircleRationalCoefficients.run price
  dsimp only
  omega

theorem bounded {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (hw : ∀ j,weights.read j≤mass) (hW : 1≤W) (hIndex : binaryWordWidth (g+1)≤W)
    (count : ℕ) (hc : count≤g) : window model W R mass weights count hc≤profile model W g R mass := by
  have hWeights := array_bound W (natBits mass) natBits weights
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (width R mass) (callbackPrice model W R mass) (scalarProfile model W R mass)
    rationalWordWidth (fun j => coordinate model.rat W R mass (weights.read j))
    (fun j => scalarWindow model W R mass (weights.read j))
    (fun j => ratio_width R mass _ (hw j)) (fun j => coordinate_work model.rat model.monotone W R mass _ (hw j))
    (fun j => scalar_bound model W R mass _ (hw j)) hW hIndex count hc
  have hWork := work model W R mass weights hw hW hIndex
  have hStored := GeneralPaperNativePayloadFillStorage.prefix_work W (callbackPrice model W R mass)
    (fun j => coordinate model.rat W R mass (weights.read j))
    (fun j => coordinate_work model.rat model.monotone W R mass _ (hw j)) hW hIndex g le_rfl
  change (PaperIndexedArrayConstruction.run (fun w => w) W
    (fun j => coordinate model.rat W R mass (weights.read j))).2≤
      GeneralPaperNativePayloadFillStorage.workCap W g (callbackPrice model W R mass) at hStored
  unfold price at hWork
  have hMass := denominator_width R mass
  have hCast := model.monotone hMass
  have hf := fields_bound W (natBits (metadataCap model W g R mass))
    [g,(PaperIndexedArrayConstruction.run (fun w => w) W (fun j => coordinate model.rat W R mass (weights.read j))).2,
      model.rat (rationalWordWidth (mass:ℚ)),16*W,(GeneralPaperCircleRationalCoefficients.run model.rat (fun w => w) W R mass weights).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap price
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (metadataCap model W g R mass)+W)+32*W at hf
  unfold window profile
  dsimp only
  nlinarith only [hWeights,hFill,hf,hMass,hCast]

end Blotto.GeneralPaperCircleCoefficientConstructionStorage
