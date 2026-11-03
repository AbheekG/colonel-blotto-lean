import Blotto.GeneralPaperEncodedRationalRows

/-! One live closed decoder, its returned fraction and cast/division
temporaries. Existing decoder branch/stack bounds are reused; rational
scratch is charged at the native operand widths, including invalid zero. -/
namespace Blotto.GeneralPaperClosedBidStorage
open GeneralPaperCodeAlphabet GeneralPaperClosedBidExecution
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def tail (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) : ℕ :=
  match (GeneralPaperCodeDecodeExecution.run true model W a false code).1.choice with
  | none => rationalWordWidth (0:ℚ)+model.rat (rationalWordWidth (0:ℚ))+128*W
  | some c => rationalWordWidth (c.threshold.num:ℚ)+rationalWordWidth (c.threshold.den:ℚ)+
    rationalWordWidth c.threshold.value+fractionWork model.rat c+128*W

def window (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) : ℕ :=
  GeneralPaperCodeDecodeStorage.window model W a false code+tail model W a code+
    rationalWordWidth (run true model W a code).1+128*W

def profile (model : RationalCostModel) (W : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCodeDecodeStorage.profile model W a+8*model.rat (width a)+256*W

theorem tail_bound (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) :
    tail model W a code≤7*model.rat (width a)+128*W := by
  cases h : (GeneralPaperCodeDecodeExecution.run true model W a false code).1.choice with
  | none =>
    have hw : rationalWordWidth (0:ℚ)≤width a := by
      rw [show rationalWordWidth (0:ℚ)=3 by decide]
      exact width_positive a
    have hm := model.monotone hw
    have hp := hw.trans (model.word_le _)
    simp only [tail,h]
    omega
  | some c =>
    have hc := h
    rw [GeneralPaperCodeDecodeExecution.data] at hc
    obtain ⟨hn,hd,hv⟩ := fraction_widths a code c hc
    have hn' := hn.trans (model.word_le _)
    have hd' := hd.trans (model.word_le _)
    have hv' := hv.trans (model.word_le _)
    have hf := fraction_work model a code c hc
    simp only [tail,h]
    omega

theorem returned (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) :
    rationalWordWidth (run true model W a code).1≤model.rat (width a) := by
  have h := rationalWordWidth_of_height (height true model W a code)
  have hC := GeneralPaperDecoderControls.code_word a a.C (by omega)
  have hw : rationalWordWidth (run true model W a code).1≤width a := by unfold width; omega
  exact hw.trans (model.word_le _)

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (code : ℕ) (hc : code≤8*a.C) :
    window model W a code≤profile model W a := by
  have hd := GeneralPaperCodeDecodeStorage.bounded model W a false code hc
  have ht := tail_bound model W a code
  have hr := returned model W a code
  unfold window profile
  omega

end Blotto.GeneralPaperClosedBidStorage
