import Blotto.GeneralPaperPhysicalShiftExecution

/-! Decode a returned response code once, construct its rational threshold
and add the retained shared shift exactly on open choices. Invalid returns
produce zero. The mathematical default choice is only a data comparator. -/
namespace Blotto.GeneralPaperPhysicalBidExecution
open GeneralPaperCodeAlphabet GeneralPaperResponsePhysicalHeights
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def decodedChoice (a : Alphabet) (code : ℕ) : Choice :=
  match (GeneralPaperCodeDecode.decode a true code).choice with
  | none => ⟨grid a 0,false⟩
  | some c => c

theorem decoded_choice_of_some (a : Alphabet) (code : ℕ) (c : Choice)
    (h : (GeneralPaperCodeDecode.decode a true code).choice=some c) : decodedChoice a code=c := by
  simp only [decodedChoice,h]

theorem threshold_height (a : Alphabet) (code : ℕ) :
    RationalHeight (decodedChoice a code).threshold.value (binaryWordWidth a.C) := by
  cases h : (GeneralPaperCodeDecode.decode a true code).choice with
  | none =>
    simp only [decodedChoice,h,grid_zero]
    exact GeneralPaperQuantizedHeight.zero_height _ (binaryWordWidth_pos _)
  | some c =>
    simp only [decodedChoice,h]
    exact decoded_threshold a true code c h

def run (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ) (code : ℕ) : ℚ × ℕ :=
  let decoded := GeneralPaperCodeDecodeExecution.run bits model W a true code
  match decoded.1.choice with
  | none => (0,decoded.2+primitive bits model (rationalWordWidth (0:ℚ))+64*W)
  | some c =>
    let value := c.threshold.value
    let physical := if c.opened then value+delta else value
    let addWork := if c.opened then
      GeneralPaperRationalPrimitivePrice.binary (primitive bits model) (fun a b => a+b) value delta else 0
    (physical,decoded.2+GeneralPaperClosedBidExecution.fractionWork (primitive bits model) c+addWork+64*W)

theorem data (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ) (code : ℕ) :
    (run bits model W a delta code).1=(decodedChoice a code).physical delta := by
  unfold run
  dsimp only
  rw [GeneralPaperCodeDecodeExecution.data]
  cases h : (GeneralPaperCodeDecode.decode a true code).choice with
  | none => simp only [decodedChoice,h,Choice.physical,Bool.false_eq_true,ite_false,add_zero,grid_zero]
  | some c =>
    cases hc : c.opened <;> simp only [decodedChoice,h,hc,Choice.physical,Bool.false_eq_true,ite_false,ite_true,add_zero]

theorem fraction_work (model : RationalCostModel) (a : Alphabet) (code : ℕ) (c : Choice)
    (hc : (GeneralPaperCodeDecode.decode a true code).choice=some c) :
    GeneralPaperClosedBidExecution.fractionWork model.rat c≤4*model.rat (GeneralPaperClosedBidExecution.width a) := by
  have hb := GeneralPaperCodeRecordStorage.decoded_bounds a true code c hc
  have hC := GeneralPaperDecoderControls.code_word a a.C (by omega)
  have hn := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.threshold.num)
  have hd := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.threshold.den)
  have hn' := binaryWordWidth_mono hb.1
  have hd' := binaryWordWidth_mono hb.2
  have hv := rationalWordWidth_of_height (decoded_threshold a true code c hc)
  have hnW : rationalWordWidth (c.threshold.num:ℚ)≤GeneralPaperClosedBidExecution.width a := by
    unfold GeneralPaperClosedBidExecution.width; omega
  have hdW : rationalWordWidth (c.threshold.den:ℚ)≤GeneralPaperClosedBidExecution.width a := by
    unfold GeneralPaperClosedBidExecution.width; omega
  have hvW : rationalWordWidth c.threshold.value≤GeneralPaperClosedBidExecution.width a := by
    unfold GeneralPaperClosedBidExecution.width; omega
  have h0 := model.monotone hnW
  have h1 := model.monotone hdW
  have h2 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    (c.threshold.num:ℚ) (c.threshold.den:ℚ) (GeneralPaperClosedBidExecution.width a) hnW hdW hvW
  unfold GeneralPaperClosedBidExecution.fractionWork
  omega

def additionWidth (m qbar t : ℕ) (a : Alphabet) : ℕ :=
  word m (binaryWordWidth a.C) (shiftHeight m qbar a.C) t

def bitProfile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperClosedBidExecution.bitProfile model W a+2*model.rat (additionWidth m qbar t a)

theorem bit_work (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (code : ℕ) (hc : code≤8*a.C) :
    (run true model W a delta code).2≤bitProfile model W m qbar t a := by
  have hDecode := GeneralPaperCodeDecodePrice.bit_work model W a true code hc
  have hw := model.monotone (show GeneralPaperDecoderControls.operandWidth a.lambda≤GeneralPaperClosedBidExecution.width a by
    unfold GeneralPaperClosedBidExecution.width; omega)
  have hDecode' := hDecode.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hw _))
  have hz := model.monotone (show rationalWordWidth (0:ℚ)≤GeneralPaperClosedBidExecution.width a by
    rw [show rationalWordWidth (0:ℚ)=3 by decide]; exact GeneralPaperClosedBidExecution.width_positive a)
  unfold run bitProfile GeneralPaperClosedBidExecution.bitProfile
  dsimp only
  cases h : (GeneralPaperCodeDecodeExecution.run true model W a true code).1.choice with
  | none => simp only [primitive,ite_true]; omega
  | some c =>
    have hc' := h
    rw [GeneralPaperCodeDecodeExecution.data] at hc'
    have hf := fraction_work model a code c hc'
    have ht := decoded_threshold a true code c hc'
    have hv := rationalWordWidth_of_height ht
    have hd' := rationalWordWidth_of_height hd
    have hvW : rationalWordWidth c.threshold.value≤additionWidth m qbar t a := by
      unfold additionWidth word bidHeight; omega
    have hdW : rationalWordWidth delta≤additionWidth m qbar t a := by
      unfold additionWidth word bidHeight; omega
    have hp := bid_word m (binaryWordWidth a.C) (shiftHeight m qbar a.C) t c ht delta hd
    cases hcOpen : c.opened with
    | false => simp only [primitive,ite_true,hcOpen,Bool.false_eq_true,ite_false]; omega
    | true =>
      have hp' : rationalWordWidth (c.threshold.value+delta)≤additionWidth m qbar t a := by
        simpa only [Choice.physical,hcOpen,ite_true,additionWidth] using hp
      have ha := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
        c.threshold.value delta (additionWidth m qbar t a) hvW hdW hp'
      simp only [primitive,ite_true,hcOpen]
      omega

theorem arithmetic_work (model : RationalCostModel) (a : Alphabet) (delta : ℚ) (code : ℕ) :
    (run false model 1 a delta code).2≤16777216*(a.lambda+3)+70 := by
  have h := GeneralPaperCodeDecodePrice.arithmetic_work model a true code
  unfold run
  dsimp only
  cases hc : (GeneralPaperCodeDecodeExecution.run false model 1 a true code).1.choice with
  | none => simp only [primitive,Bool.false_eq_true,ite_false]; omega
  | some c =>
    cases ho : c.opened with
    | false =>
      simp only [primitive,Bool.false_eq_true,ite_false,ho,
        GeneralPaperClosedBidExecution.fractionWork,GeneralPaperRationalPrimitivePrice.binary]
      omega
    | true =>
      simp only [primitive,Bool.false_eq_true,ite_false,ite_true,ho,
        GeneralPaperClosedBidExecution.fractionWork,GeneralPaperRationalPrimitivePrice.binary]
      omega

end Blotto.GeneralPaperPhysicalBidExecution
