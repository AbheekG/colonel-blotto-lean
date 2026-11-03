import Blotto.GeneralPaperCircleSortedScale

/-! Native rational light-bid coefficients R*w/W constructed once from
retained integer weights. Products, casts, division/result writes and all
array accesses are priced; native input height inspection is not used. -/
namespace Blotto.GeneralPaperCircleRationalCoefficients
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000

def coordinate (price : ℕ → ℕ) (A R : ℕ) (q : ℚ) (w : ℕ) : ℚ × ℕ :=
  let product := R*w
  ((product:ℚ)/q,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) R w+
    price (rationalWordWidth (product:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary price (fun a b => a/b) product q+64*A)

def run {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) : FixedArrayTable g ℚ × ℕ :=
  let q : ℚ := W
  let stored := PaperIndexedArrayConstruction.run index A (fun j => coordinate price A R q (weights.read j))
  (stored.1,stored.2+price (rationalWordWidth q)+16*A)

theorem data {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) :
    (run price index A R W weights).1=FixedArrayTable.ofFn (fun j => ((R*weights.read j:ℕ):ℚ)/W) := by
  unfold run
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]
  rfl

theorem real_data {g : ℕ} (price index : ℕ → ℕ) (A R W : ℕ) (weights : FixedArrayTable g ℕ) (j : Fin g) :
    ((run price index A R W weights).1.read j:ℝ)=GeneralPaperCircleCoordinatePayoff.coefficient R W (weights.read j) := by
  rw [data,FixedArrayTable.read_ofFn]
  simp only [GeneralPaperCircleCoordinatePayoff.coefficient,Rat.cast_div,Rat.cast_natCast]

def width (R W : ℕ) : ℕ := 64+16*(binaryWordWidth R+binaryWordWidth W)

theorem product_width (R W w : ℕ) (hw : w≤W) : rationalWordWidth ((R*w:ℕ):ℚ)≤width R W := by
  have h := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height (R*w))
  have hm := binaryWordWidth_mul R w
  have hw' := binaryWordWidth_mono hw
  unfold width
  omega

theorem denominator_width (R W : ℕ) : rationalWordWidth (W:ℚ)≤width R W := by
  have h := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height W)
  unfold width
  omega

theorem ratio_height (R W w : ℕ) (hw : w≤W) :
    RationalHeight (((R*w:ℕ):ℚ)/W) (binaryWordWidth R+2*binaryWordWidth W) := by
  have hp := (GeneralPaperBasisDivideBits.nat_height (R*w)).mono
    ((binaryWordWidth_mul R w).trans (Nat.add_le_add_left (binaryWordWidth_mono hw) (binaryWordWidth R)))
  have h := hp.div (GeneralPaperBasisDivideBits.nat_height W)
  exact h.mono (by omega)

theorem ratio_width (R W w : ℕ) (hw : w≤W) : rationalWordWidth (((R*w:ℕ):ℚ)/W)≤width R W := by
  have h := rationalWordWidth_of_height (ratio_height R W w hw)
  unfold width
  omega

theorem coordinate_work (price : ℕ → ℕ) (hMono : Monotone price) (A R W w : ℕ) (hw : w≤W) :
    (coordinate price A R W w).2≤5*price (width R W)+64*A := by
  have hw' := binaryWordWidth_mono hw
  have hp := binaryWordWidth_mul R w
  have hm := GeneralPaperIntegerWordPrice.natural_binary price hMono (fun a b => a*b) R w (width R W)
    (by unfold width;omega) (by unfold width;omega) (by unfold width;omega)
  have hc := hMono (product_width R W w hw)
  have hd := GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a/b) (R*w:ℕ) W (width R W)
    (product_width R W w hw) (denominator_width R W) (ratio_width R W w hw)
  unfold coordinate
  dsimp only
  omega

theorem work {g : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A R W : ℕ) (hA : 1≤A)
    (weights : FixedArrayTable g ℕ) (hw : ∀ j,weights.read j≤W)
    (hIndex : ∀ i≤g,index (binaryWordWidth (i+1))≤A) :
    (run price index A R W weights).2≤g*(5*price (width R W)+64*A)+44*(g+1)*A+price (width R W)+16*A := by
  have ha := GeneralPaperControlArrayPrice.indexed_work index A (5*price (width R W)+64*A)
    (fun j => coordinate price A R W (weights.read j)) hA hIndex (fun j => coordinate_work price hMono A R W _ (hw j))
  have hd := hMono (denominator_width R W)
  change (PaperIndexedArrayConstruction.run index A (fun j => coordinate price A R W (weights.read j))).2+
    price (rationalWordWidth (W:ℚ))+16*A≤_
  omega

end Blotto.GeneralPaperCircleRationalCoefficients
