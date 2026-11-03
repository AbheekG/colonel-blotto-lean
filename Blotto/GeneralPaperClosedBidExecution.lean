import Blotto.GeneralPaperSharpSourceSpaceContract

/-! Materialize one stored closed candidate code as a rational bid. The
native decoder runs once; closed choices need no open-bid shift. Prices
include the two casts, division/result write, invalid zero and references. -/
namespace Blotto.GeneralPaperClosedBidExecution
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def fractionWork (price : ℕ → ℕ) (c : Choice) : ℕ :=
  price (rationalWordWidth (c.threshold.num:ℚ))+price (rationalWordWidth (c.threshold.den:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary price (fun a b => a/b) (c.threshold.num:ℚ) (c.threshold.den:ℚ)

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) : ℚ × ℕ :=
  let decoded := GeneralPaperCodeDecodeExecution.run bits model W a false code
  match decoded.1.choice with
  | none => (0,decoded.2+primitive bits model (rationalWordWidth (0:ℚ))+64*W)
  | some c => (c.threshold.value,decoded.2+fractionWork (primitive bits model) c+64*W)

theorem data (bits : Bool) (model : RationalCostModel) (W m qbar : ℕ) (a : Alphabet) (code : ℕ) :
    (run bits model W a code).1=GeneralPaperCatalogueRationalTrajectory.decodeValue m qbar a code := by
  unfold run
  dsimp only
  rw [GeneralPaperCodeDecodeExecution.data]
  cases hc : (GeneralPaperCodeDecode.decode a false code).choice with
  | none => simp only [GeneralPaperCatalogueRationalTrajectory.decodeValue,hc]
  | some c =>
    have h := GeneralPaperCodeDecodeSound.candidate_closed a code c hc
    simp only [GeneralPaperCatalogueRationalTrajectory.decodeValue,hc,Choice.physical,h,
      Bool.false_eq_true,ite_false,add_zero]

theorem height (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) :
    RationalHeight (run bits model W a code).1 (binaryWordWidth a.C) := by
  rw [data bits model W 0 0]
  exact GeneralPaperSourceScoreHeights.decoded_height 0 0 a code

def width (a : Alphabet) : ℕ := 4*operandWidth a.lambda

theorem width_positive (a : Alphabet) : 3≤width a := by unfold width operandWidth; omega

theorem fraction_widths (a : Alphabet) (code : ℕ) (c : Choice)
    (hc : (GeneralPaperCodeDecode.decode a false code).choice=some c) :
    rationalWordWidth (c.threshold.num:ℚ)≤width a ∧
    rationalWordWidth (c.threshold.den:ℚ)≤width a ∧ rationalWordWidth c.threshold.value≤width a := by
  have hb := GeneralPaperCodeRecordStorage.decoded_bounds a false code c hc
  have hC := code_word a a.C (by omega)
  have hn := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.threshold.num)
  have hd := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.threshold.den)
  have hn' := binaryWordWidth_mono hb.1
  have hd' := binaryWordWidth_mono hb.2
  have hv := GeneralPaperSourceScoreHeights.decoded_height 0 0 a code
  have hClosed := GeneralPaperCodeDecodeSound.candidate_closed a code c hc
  simp only [GeneralPaperCatalogueRationalTrajectory.decodeValue,hc,Choice.physical,hClosed,
    Bool.false_eq_true,ite_false,add_zero] at hv
  have hv' := rationalWordWidth_of_height hv
  unfold width
  omega

theorem fraction_work (model : RationalCostModel) (a : Alphabet) (code : ℕ) (c : Choice)
    (hc : (GeneralPaperCodeDecode.decode a false code).choice=some c) :
    fractionWork model.rat c≤4*model.rat (width a) := by
  obtain ⟨hn,hd,hv⟩ := fraction_widths a code c hc
  have h1 := model.monotone hn
  have h2 := model.monotone hd
  have h3 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    (c.threshold.num:ℚ) (c.threshold.den:ℚ) (width a) hn hd hv
  unfold fractionWork
  omega

def bitProfile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  8388608*(a.lambda+3)*(controlWord W a.lambda+model.rat (width a))+
    4*model.rat (width a)+64*W

def arithmeticProfile (a : Alphabet) : ℕ := 16777216*(a.lambda+3)+68

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hc : code≤8*a.C) :
    (run true model W a code).2≤bitProfile model W a := by
  have hDecode := GeneralPaperCodeDecodePrice.bit_work model W a false code hc
  have hw := model.monotone (show operandWidth a.lambda≤width a by unfold width; omega)
  have hz := model.monotone (show rationalWordWidth (0:ℚ)≤width a by
    rw [show rationalWordWidth (0:ℚ)=3 by decide]; exact width_positive a)
  have hDecode' : (GeneralPaperCodeDecodeExecution.run true model W a false code).2≤
      8388608*(a.lambda+3)*(controlWord W a.lambda+model.rat (width a)) :=
    hDecode.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hw _))
  unfold run bitProfile
  dsimp only
  cases h : (GeneralPaperCodeDecodeExecution.run true model W a false code).1.choice with
  | none => simp only [primitive,ite_true]; omega
  | some c =>
    have hc' := h
    rw [GeneralPaperCodeDecodeExecution.data] at hc'
    have hf := fraction_work model a code c hc'
    simp only [primitive,ite_true]
    omega

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (code : ℕ) :
    (run false model 1 a code).2≤arithmeticProfile a := by
  have h := GeneralPaperCodeDecodePrice.arithmetic_work model a false code
  unfold run arithmeticProfile
  dsimp only
  cases hc : (GeneralPaperCodeDecodeExecution.run false model 1 a false code).1.choice <;>
    simp only [primitive,Bool.false_eq_true,ite_false,fractionWork,
      GeneralPaperRationalPrimitivePrice.binary] <;> omega

theorem same_data (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) :
    (run true model W a code).1=(run false model 1 a code).1 := by
  rw [data true model W 0 0,data false model 1 0 0]

end Blotto.GeneralPaperClosedBidExecution
