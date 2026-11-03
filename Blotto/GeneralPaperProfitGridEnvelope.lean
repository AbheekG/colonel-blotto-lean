import Blotto.GeneralPaperProfitGridPrice

/-! All grid operand and local reference/control widths follow from the
retained source parameters. These are analytical bounds; their evaluation
adds no pass over the input, grid or original rational encodings.
-/
namespace Blotto.GeneralPaperProfitGridEnvelope
open GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 8000000

structure Sizes (m lambda k Qv : ℕ) : Prop where
  q : binaryWordWidth (GeneralPaperProfitParameters.parameters m lambda k Qv).qProf≤32*measure m lambda k Qv
  width : binaryWordWidth ((GeneralPaperProfitParameters.parameters m lambda k Qv).width+1)≤16*measure m lambda k Qv
  exponent : (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent≤32*measure m lambda k Qv
  capacity : binaryWordWidth (GeneralPaperProfitOrderPrice.capacity
    (GeneralPaperProfitParameters.parameters m lambda k Qv).width
    (GeneralPaperProfitParameters.parameters m lambda k Qv).exponent)≤64*measure m lambda k Qv

theorem sizes (m lambda k Qv : ℕ) : Sizes m lambda k Qv := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let M := measure m lambda k Qv
  have hs := GeneralPaperSourcePreparationSizes.sizes m lambda k Qv
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  have hQ := hs.profitExponentTarget
  change binaryWordWidth (4*p.qProf)≤32*M at hQ
  have hQmono := binaryWordWidth_mono (show p.qProf≤4*p.qProf by omega)
  have hQBound : binaryWordWidth p.qProf≤32*M := hQmono.trans hQ
  have hw := GeneralPaperParameterOperandBounds.ceiling_word (GeneralPaperProfitParameterPrice.widthTarget m k)
  change binaryWordWidth p.width≤4+binaryWordWidth (GeneralPaperProfitParameterPrice.widthTarget m k) at hw
  have hTarget := hs.profitWidthTarget
  change binaryWordWidth (GeneralPaperProfitParameterPrice.widthTarget m k)≤8*M at hTarget
  have hwPlus := GeneralPaperRayOperandWidthEnvelope.word_add p.width 1
  have h1 : binaryWordWidth 1=1 := by decide
  have hWidth : binaryWordWidth (p.width+1)≤16*M := by omega
  have hB := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).exponent
  change p.exponent≤32*M at hB
  have hbWord := GeneralPaperInitializerControlCounters.word_le_self (p.exponent+1)
  have hMul := binaryWordWidth_mul (p.exponent+1) (p.width+1)
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add ((p.exponent+1)*(p.width+1)) 3
  have h3 : binaryWordWidth 3=2 := by decide
  refine ⟨hQBound,hWidth,hB,?_⟩
  change binaryWordWidth ((p.exponent+1)*(p.width+1)+3)≤64*M
  omega

theorem widths (m lambda k Qv : ℕ) :
    let p := GeneralPaperProfitParameters.parameters m lambda k Qv
    let H := GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv
    GeneralPaperProfitPointPrice.width p.width p.exponent≤H ∧
      GeneralPaperProfitScalePrice.width p.qProf p.width p.exponent≤H ∧
      2*GeneralPaperProfitOrderPrice.word p.width p.exponent≤H ∧
      1+binaryWordWidth (2*GeneralPaperProfitGridPoints.denominator p.width p.exponent)≤H ∧
      1+binaryWordWidth (2*(GeneralPaperProfitGridPrice.count p.width p.exponent+2))≤H := by
  let p := GeneralPaperProfitParameters.parameters m lambda k Qv
  let M := measure m lambda k Qv
  have hs := sizes m lambda k Qv
  have hQ := hs.q
  have hW := hs.width
  have hB := hs.exponent
  have hCap := hs.capacity
  change binaryWordWidth p.qProf≤32*M at hQ
  change binaryWordWidth (p.width+1)≤16*M at hW
  change p.exponent≤32*M at hB
  change binaryWordWidth (GeneralPaperProfitOrderPrice.capacity p.width p.exponent)≤64*M at hCap
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  have hp := GeneralPaperNatPowerOperands.power_width 2 p.exponent
  have hw := binaryWordWidth_mono (show p.width≤p.width+1 by omega)
  have hd := binaryWordWidth_mul (2^p.exponent) p.width
  have hu := binaryWordWidth_mul 2 (GeneralPaperProfitGridPoints.denominator p.width p.exponent)
  change binaryWordWidth (GeneralPaperProfitGridPoints.denominator p.width p.exponent)≤_ at hd
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hp hu
  have hCount : GeneralPaperProfitGridPrice.count p.width p.exponent+2≤GeneralPaperProfitOrderPrice.capacity p.width p.exponent+1 := by
    unfold GeneralPaperProfitGridPrice.count GeneralPaperProfitOrderPrice.capacity
    nlinarith only [Nat.zero_le p.exponent]
  have hc := binaryWordWidth_mono hCount
  have hcPlus := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperProfitOrderPrice.capacity p.width p.exponent) 1
  have hDepth := binaryWordWidth_mul 2 (GeneralPaperProfitGridPrice.count p.width p.exponent+2)
  have h1 : binaryWordWidth 1=1 := by decide
  rw [h2] at hDepth
  change GeneralPaperProfitPointPrice.width p.width p.exponent≤1048576*M ∧
    GeneralPaperProfitScalePrice.width p.qProf p.width p.exponent≤1048576*M ∧
    2*GeneralPaperProfitOrderPrice.word p.width p.exponent≤1048576*M ∧
    1+binaryWordWidth (2*GeneralPaperProfitGridPoints.denominator p.width p.exponent)≤1048576*M ∧
    1+binaryWordWidth (2*(GeneralPaperProfitGridPrice.count p.width p.exponent+2))≤1048576*M
  unfold GeneralPaperProfitPointPrice.width GeneralPaperProfitScalePrice.width GeneralPaperProfitOrderPrice.word
  omega

theorem dyadic_controls (primitive : ℕ → ℕ) (w B h : ℕ) (hh : h≤B) :
    let W := GeneralPaperProfitOrderPrice.word w B
    binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive W h).1.doublings+1)≤W ∧
      binaryWordWidth ((GeneralPaperDyadicPowerBits.run primitive W h).1.work+8)≤W := by
  have hB : B+1≤GeneralPaperProfitOrderPrice.capacity w B := by
    unfold GeneralPaperProfitOrderPrice.capacity
    nlinarith only [Nat.zero_le w]
  have hb := binaryWordWidth_mono hB
  apply GeneralPaperParameterCounterWords.dyadic_prefix primitive _ B h hh
  unfold GeneralPaperProfitOrderPrice.word
  omega

end Blotto.GeneralPaperProfitGridEnvelope
