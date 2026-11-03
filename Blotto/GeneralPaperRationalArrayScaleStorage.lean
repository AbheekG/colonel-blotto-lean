import Blotto.GeneralPaperSourceStrictChildReachedRates

/-! Literal rational output-scale constructor, also used by native unit
normalization. Actual operands/product, one multiply scratch, callback
prefixes, full input/output arrays and all constructor buffers/frames coexist.
Only primitive work is scratch; traversal work sizes encoded fields. -/
namespace Blotto.GeneralPaperRationalArrayScaleStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def callback (model : RationalCostModel) (W : ℕ) (c x : ℚ) : ℚ×ℕ :=
  (c*x,GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) c x+64*W)
def callbackPrice (model : RationalCostModel) (W R : ℕ) : ℕ := 2*model.rat R+64*W
def scalarCap (model : RationalCostModel) (W R : ℕ) : ℕ := callbackPrice model W R+1
def scalarControls (model : RationalCostModel) (W : ℕ) (c x : ℚ) : List ℕ :=
  let a := model.rat (RationalExpression.pairWidth c x)
  let b := model.rat (rationalWordWidth (c*x))
  [a,b,a+b,a+b+64*W,64*W]
def scalarWindow (model : RationalCostModel) (W : ℕ) (c x : ℚ) : ℕ :=
  rationalWordWidth c+rationalWordWidth x+rationalWordWidth (c*x)+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a*b) c x+
    fields W (scalarControls model W c x)+128*W
def scalarProfile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  3*R+2*model.rat R+5*(natBits (scalarCap model W R)+W)+160*W
def price (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W n (callbackPrice model W R)
def metadataCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+price model W n R+64*W+1
def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ) (count : ℕ) (hc : count≤n) : ℕ :=
  arrayFootprint W rationalWordWidth values+rationalWordWidth c+
    GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (fun j => callback model W c (values.read j))
      (fun j => scalarWindow model W c (values.read j)) count hc+
    fields W [n,(GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c values).2,64*W]+128*W
def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  arrayProfile W n R+R+GeneralPaperNativePayloadFillStorage.profile W R n (callbackPrice model W R) (scalarProfile model W R)+
    3*(natBits (metadataCap model W n R)+W)+160*W

theorem callback_work (model : RationalCostModel) (W R : ℕ) (c x : ℚ)
    (hc : rationalWordWidth c≤R) (hx : rationalWordWidth x≤R) (hp : rationalWordWidth (c*x)≤R) :
    (callback model W c x).2≤callbackPrice model W R :=
  Nat.add_le_add_right (GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) c x R hc hx hp) _

theorem scalar_bound (model : RationalCostModel) (W R : ℕ) (c x : ℚ)
    (hc : rationalWordWidth c≤R) (hx : rationalWordWidth x≤R) (hp : rationalWordWidth (c*x)≤R) :
    scalarWindow model W c x≤scalarProfile model W R := by
  have hi := model.monotone (max_le hc hx)
  have ho := model.monotone hp
  have hWork := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) c x R hc hx hp
  have hf := fields_bound W (natBits (scalarCap model W R)) (scalarControls model W c x) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold scalarControls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold scalarCap callbackPrice
    change model.rat (RationalExpression.pairWidth c x)≤model.rat R at hi
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (scalarCap model W R)+W)+32*W at hf
  unfold scalarWindow scalarProfile
  omega

theorem work {n : ℕ} (model : RationalCostModel) (W R : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ)
    (hc : rationalWordWidth c≤R) (hx : ∀ j,rationalWordWidth (values.read j)≤R)
    (hp : ∀ j,rationalWordWidth (c*values.read j)≤R) (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W) :
    (GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c values).2≤price model W n R :=
  GeneralPaperNativePayloadFillStorage.prefix_work W _ (fun j => callback model W c (values.read j))
    (fun j => callback_work model W R c (values.read j) hc (hx j) (hp j)) hW hIndex n le_rfl

theorem bounded {n : ℕ} (model : RationalCostModel) (W R : ℕ) (c : ℚ) (values : FixedArrayTable n ℚ)
    (hc : rationalWordWidth c≤R) (hx : ∀ j,rationalWordWidth (values.read j)≤R)
    (hp : ∀ j,rationalWordWidth (c*values.read j)≤R) (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W)
    (count : ℕ) (hCount : count≤n) : window model W c values count hCount≤profile model W n R := by
  have hArray := array_bound W R rationalWordWidth values hx
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (callbackPrice model W R) (scalarProfile model W R) rationalWordWidth
    (fun j => callback model W c (values.read j)) (fun j => scalarWindow model W c (values.read j)) hp
    (fun j => callback_work model W R c (values.read j) hc (hx j) (hp j))
    (fun j => scalar_bound model W R c (values.read j) hc (hx j) (hp j)) hW hIndex count hCount
  have hWork := work model W R c values hc hx hp hW hIndex
  have hf := fields_bound W (natBits (metadataCap model W n R))
    [n,(GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c values).2,64*W] (by
      intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold metadataCap
      rcases hz with rfl|rfl|rfl <;> omega)
  change fields W _≤3*(natBits (metadataCap model W n R)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperRationalArrayScaleStorage
