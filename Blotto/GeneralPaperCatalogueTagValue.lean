import Blotto.GeneralPaperCatalogueArraysExecution

/-! A tag evaluates its retained fraction using two casts and one rational
division, including the written result. Actual decoder numerator/denominator
caps derive full-code operand words; floating-point mantissa words are not used.
-/
namespace Blotto.GeneralPaperCatalogueTagValue
open GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (price : ℕ → ℕ) (W : ℕ) (f : Farey.Fraction) (opened : Bool) : GeneralPaperResponseTag.Tag × ℕ :=
  (⟨f.value,opened⟩,price (rationalWordWidth (f.num:ℚ))+price (rationalWordWidth (f.den:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary price (fun a b => a/b) (f.num:ℚ) (f.den:ℚ)+64*W)

theorem words (a : Alphabet) (f : Farey.Fraction) (hNum : f.num≤a.C) (hDen : f.den≤a.C) :
    rationalWordWidth (f.num:ℚ)≤operandWidth a.lambda ∧
    rationalWordWidth (f.den:ℚ)≤operandWidth a.lambda ∧ rationalWordWidth f.value≤operandWidth a.lambda := by
  have hC : a.C<2^a.lambda := by rw [←a.dyadic]; have hp := a.scalePositive; omega
  have height (x : ℕ) (hx : x≤a.C) : RationalHeight (x:ℚ) (a.lambda+1) :=
    (GeneralPaperBasisDivideBits.nat_height x).mono (GeneralPaperCFOperandPrice.small_word a.lambda x (hx.trans_lt hC))
  have hn := height f.num hNum
  have hd := height f.den hDen
  have wn := rationalWordWidth_of_height hn
  have wd := rationalWordWidth_of_height hd
  have wv := rationalWordWidth_of_height (hn.div hd)
  change rationalWordWidth f.value≤_ at wv
  unfold operandWidth
  exact ⟨wn.trans (by omega),wd.trans (by omega),wv.trans (by omega)⟩

theorem bit_work (model : RationalCostModel) (W : ℕ) (a : Alphabet) (f : Farey.Fraction)
    (hNum : f.num≤a.C) (hDen : f.den≤a.C) (opened : Bool) :
    (run model.rat W f opened).2≤4*model.rat (operandWidth a.lambda)+64*W := by
  have hw := words a f hNum hDen
  have hn := model.monotone hw.1
  have hd := model.monotone hw.2.1
  have hv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    (f.num:ℚ) (f.den:ℚ) (operandWidth a.lambda) hw.1 hw.2.1 hw.2.2
  unfold run
  dsimp only
  omega

theorem arithmetic_work (f : Farey.Fraction) (opened : Bool) : (run (fun _ => 1) 1 f opened).2=68 := rfl

theorem native_bounds {m : ℕ} (a : Alphabet) (response : Bool) (k : ℕ)
    (summaries : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Summary k))
    (data : GeneralPaperCatalogueArrays.Arrays m ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hData : data=GeneralPaperCatalogueArrays.prepare a response k summaries)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    ((data.thresholds.read j).read i).num≤a.C ∧ ((data.thresholds.read j).read i).den≤a.C := by
  subst data
  have hd := GeneralPaperCatalogueArrays.denominator a response k summaries j i
  have he := GeneralPaperCatalogueArrays.decoded_entry a response k summaries j i
  have ho := GeneralPaperCodeOrder.decoded_threshold_le_one a response _ _ he
  have hn := Farey.num_le_den _ ho
  rw [GeneralPaperCatalogueArrays.thresholds_read]
  rw [GeneralPaperCatalogueArrays.thresholds_read] at hd
  exact ⟨hn.trans hd,hd⟩

end Blotto.GeneralPaperCatalogueTagValue
