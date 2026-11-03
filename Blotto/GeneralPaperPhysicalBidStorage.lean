import Blotto.GeneralPaperPhysicalResponseRowsContract

/-! The true-mode decoder, fractional casts/division, optional open-bid
addition and returned physical value have separate live owners. Only one
active primitive's operand scratch is reserved. Shift data is borrowed. -/
namespace Blotto.GeneralPaperPhysicalBidStorage
open GeneralPaperCodeAlphabet GeneralPaperPhysicalBidExecution GeneralPaperResponsePhysicalHeights
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def height (m qbar : ℕ) (a : Alphabet) : ℕ := bidHeight (binaryWordWidth a.C) (shiftHeight m qbar a.C)

theorem returned_height (bits : Bool) (model : RationalCostModel) (W m qbar : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (code : ℕ) :
    RationalHeight (run bits model W a delta code).1 (height m qbar a) := by
  rw [data]
  exact bid_height _ _ _ (threshold_height a code) delta hd

theorem returned_word (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (code : ℕ) :
    rationalWordWidth (run true model W a delta code).1≤additionWidth m qbar t a := by
  rw [data]
  exact bid_word m _ _ t _ (threshold_height a code) delta hd

theorem fraction_words (a : Alphabet) (code : ℕ) (c : Choice)
    (hc : (GeneralPaperCodeDecode.decode a true code).choice=some c) :
    rationalWordWidth (c.threshold.num:ℚ)≤GeneralPaperClosedBidExecution.width a ∧
      rationalWordWidth (c.threshold.den:ℚ)≤GeneralPaperClosedBidExecution.width a ∧
      rationalWordWidth c.threshold.value≤GeneralPaperClosedBidExecution.width a := by
  have hb := GeneralPaperCodeRecordStorage.decoded_bounds a true code c hc
  have hC := GeneralPaperDecoderControls.code_word a a.C (by omega)
  have hn := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.threshold.num)
  have hd := rationalWordWidth_of_height (GeneralPaperBasisDivideBits.nat_height c.threshold.den)
  have hn' := binaryWordWidth_mono hb.1
  have hd' := binaryWordWidth_mono hb.2
  have hv := rationalWordWidth_of_height (decoded_threshold a true code c hc)
  unfold GeneralPaperClosedBidExecution.width
  omega

def tail (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ) (code : ℕ) : ℕ :=
  match (GeneralPaperCodeDecodeExecution.run true model W a true code).1.choice with
  | none => rationalWordWidth (0:ℚ)+model.rat (rationalWordWidth (0:ℚ))+128*W
  | some c =>
    rationalWordWidth (c.threshold.num:ℚ)+rationalWordWidth (c.threshold.den:ℚ)+
      rationalWordWidth c.threshold.value+GeneralPaperClosedBidExecution.fractionWork model.rat c+
      rationalWordWidth delta+rationalWordWidth (c.physical delta)+
      (if c.opened then GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a+b) c.threshold.value delta else 0)+128*W

theorem tail_bound (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (code : ℕ) :
    tail model W a delta code≤8*model.rat (GeneralPaperClosedBidExecution.width a)+
      4*model.rat (additionWidth m qbar t a)+128*W := by
  cases h : (GeneralPaperCodeDecodeExecution.run true model W a true code).1.choice with
  | none =>
    have hz : rationalWordWidth (0:ℚ)≤GeneralPaperClosedBidExecution.width a := by
      rw [show rationalWordWidth (0:ℚ)=3 by decide]
      exact GeneralPaperClosedBidExecution.width_positive a
    have hp := model.monotone hz
    have hw := hz.trans (model.word_le _)
    simp only [tail,h]
    omega
  | some c =>
    have hc := h
    rw [GeneralPaperCodeDecodeExecution.data] at hc
    obtain ⟨hn,hdn,hv⟩ := fraction_words a code c hc
    have hn' := hn.trans (model.word_le _)
    have hdn' := hdn.trans (model.word_le _)
    have hv' := hv.trans (model.word_le _)
    have hf := fraction_work model a code c hc
    have ht := decoded_threshold a true code c hc
    have hval := rationalWordWidth_of_height ht
    have hdelta := rationalWordWidth_of_height hd
    have hvW : rationalWordWidth c.threshold.value≤additionWidth m qbar t a := by
      unfold additionWidth word bidHeight; omega
    have hdW : rationalWordWidth delta≤additionWidth m qbar t a := by
      unfold additionWidth word bidHeight; omega
    have hpW : rationalWordWidth (c.physical delta)≤additionWidth m qbar t a :=
      bid_word m (binaryWordWidth a.C) (shiftHeight m qbar a.C) t c ht delta hd
    have hd' := hdW.trans (model.word_le _)
    have hp' := hpW.trans (model.word_le _)
    cases ho : c.opened with
    | false => simp only [tail,h,ho,Bool.false_eq_true,ite_false]; omega
    | true =>
      have hsum : rationalWordWidth (c.threshold.value+delta)≤additionWidth m qbar t a := by
        simpa only [Choice.physical,ho,ite_true] using hpW
      have ha := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
        c.threshold.value delta (additionWidth m qbar t a) hvW hdW hsum
      simp only [tail,h,ho,ite_true]
      omega

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (delta : ℚ) (code : ℕ) : ℕ :=
  GeneralPaperCodeDecodeStorage.window model W a true code+tail model W a delta code+
    rationalWordWidth (run true model W a delta code).1+128*W

def profile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCodeDecodeStorage.profile model W a+8*model.rat (GeneralPaperClosedBidExecution.width a)+
    5*model.rat (additionWidth m qbar t a)+256*W

theorem bounded (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (code : ℕ) (hc : code≤8*a.C) :
    window model W a delta code≤profile model W m qbar t a := by
  have hDecode := GeneralPaperCodeDecodeStorage.bounded model W a true code hc
  have ht := tail_bound model W m qbar t a delta hd code
  have hr := (returned_word model W m qbar t a delta hd code).trans (model.word_le _)
  unfold window profile
  omega

end Blotto.GeneralPaperPhysicalBidStorage
