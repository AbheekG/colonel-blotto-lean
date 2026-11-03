import Blotto.GeneralPaperActualCatalogueArrayStorage

/-! The native fraction-to-tag callback retains its raw fraction, two cast
results, quotient/tag and literal scalar controls through the division.
The complete primitive price conservatively reserves arithmetic scratch. -/
namespace Blotto.GeneralPaperTagValueStorage
open GeneralPaperCodeAlphabet GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem fraction (W : ℕ) (a : Alphabet) (f : Farey.Fraction)
    (hn : f.num≤a.C) (hd : f.den≤a.C) :
    GeneralPaperEncodedCatalogueStorage.fractionBits W f≤2*GeneralPaperDecoderControls.operandWidth a.lambda+16*W := by
  have hc := (GeneralPaperEpochCacheCodeWords.alphabet_scalars a).2.1
  have hnum := (Nat.add_le_add_left (binaryWordWidth_mono hn) 1).trans hc
  have hden := (Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans hc
  unfold GeneralPaperEncodedCatalogueStorage.fractionBits GeneralPaperEncodedCatalogueStorage.codeBits
  omega

theorem tag (model : RationalCostModel) (W : ℕ) (a : Alphabet) (f : Farey.Fraction)
    (hn : f.num≤a.C) (hd : f.den≤a.C) (opened : Bool) :
    GeneralPaperEncodedOptionCache.tagBits W (GeneralPaperCatalogueTagValue.run model.rat W f opened).1≤
      GeneralPaperDecoderControls.operandWidth a.lambda+1+16*W := by
  have h := (GeneralPaperCatalogueTagValue.words a f hn hd).2.2
  change rationalWordWidth f.value+1+16*W≤_
  omega

def window (model : RationalCostModel) (W : ℕ) (f : Farey.Fraction) (opened : Bool) : ℕ :=
  GeneralPaperEncodedCatalogueStorage.fractionBits W f+fields W [f.num,f.den]+
    rationalWordWidth (f.num:ℚ)+rationalWordWidth (f.den:ℚ)+
    GeneralPaperEncodedOptionCache.tagBits W (GeneralPaperCatalogueTagValue.run model.rat W f opened).1+
    (GeneralPaperCatalogueTagValue.run model.rat W f opened).2+128*W

def profile (model : RationalCostModel) (W lambda : ℕ) : ℕ :=
  let L := GeneralPaperDecoderControls.operandWidth lambda
  (2*L+16*W)+(2*(L+W)+32*W)+2*L+(L+1+16*W)+(4*model.rat L+64*W)+128*W

theorem bounded (model : RationalCostModel) (W : ℕ) (a : Alphabet) (f : Farey.Fraction)
    (hn : f.num≤a.C) (hd : f.den≤a.C) (opened : Bool) : window model W f opened≤profile model W a.lambda := by
  have hf := fraction W a f hn hd
  have ht := tag model W a f hn hd opened
  have hw := GeneralPaperCatalogueTagValue.words a f hn hd
  have hp := GeneralPaperCatalogueTagValue.bit_work model W a f hn hd opened
  have hc := (GeneralPaperEpochCacheCodeWords.alphabet_scalars a).2.1
  have hnum := (Nat.add_le_add_left (binaryWordWidth_mono hn) 1).trans hc
  have hden := (Nat.add_le_add_left (binaryWordWidth_mono hd) 1).trans hc
  have hs := fields_bound W (GeneralPaperDecoderControls.operandWidth a.lambda) [f.num,f.den] (by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hx|hx|hx
    · rw [hx]; exact hnum
    · rw [hx]; exact hden
    · cases hx)
  change fields W [f.num,f.den]≤2*(GeneralPaperDecoderControls.operandWidth a.lambda+W)+32*W at hs
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperTagValueStorage
