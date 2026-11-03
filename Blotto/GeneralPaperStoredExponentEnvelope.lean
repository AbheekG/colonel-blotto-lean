import Blotto.GeneralPaperQuantileExponentRange

/-! The paper exponent magnitude can be large, but its encoded word is
linear in the retained parameter measure. Actual bounded stored operands
therefore discharge the fast product's exponent-width premises.
-/
namespace Blotto.GeneralPaperStoredExponentEnvelope
open GeneralPaperSourcePreparationSizes GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem word_bound (m lambda k Qv : ℕ) :
    binaryWordWidth (GeneralPaperQuantileExponentRange.cap lambda k)≤256*measure m lambda k Qv := by
  let M := measure m lambda k Qv
  let G := GeneralPaperPowerPrecision.levelBound lambda k
  let p := (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
  have hG := (GeneralPaperSourcePreparationSizes.sizes m lambda k Qv).columnsTarget
  change binaryWordWidth (G+1)≤32*M at hG
  have hGmono := binaryWordWidth_mono (show G≤G+1 by omega)
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change p≤128*M at hp
  have hpWord := GeneralPaperInitializerControlCounters.word_le_self p
  have hLambda : binaryWordWidth lambda≤M := by
    have hm := binaryWordWidth_mono (show lambda≤lambda+1 by omega)
    dsimp [M,GeneralPaperSourcePreparationSizes.measure]
    omega
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  have hA := GeneralPaperRayOperandWidthEnvelope.word_add lambda G
  have hB := GeneralPaperRayOperandWidthEnvelope.word_add (lambda+G) p
  have hC := GeneralPaperRayOperandWidthEnvelope.word_add (lambda+G+p) 8
  have h8 : binaryWordWidth 8=4 := by decide
  change binaryWordWidth (lambda+G+p+8)≤256*M
  omega

theorem multiply_width (m lambda k Qv : ℕ) (left right : Number)
    (hl : left.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k)
    (hr : right.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    GeneralPaperDyadicMultiplyPrice.width (GeneralPaperPowerPrecision.prepare lambda k).unit
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits left right≤
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let M := measure m lambda k Qv
  have hL := (binaryWordWidth_mono hl).trans (word_bound m lambda k Qv)
  have hR := (binaryWordWidth_mono hr).trans (word_bound m lambda k Qv)
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change f.fractionalBits≤128*M at hp
  have hPWord := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hUnit := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data f.fractionalBits).1,
    ←GeneralPaperPowerPrecision.unit_power lambda k] at hUnit
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  change GeneralPaperDyadicMultiplyPrice.width f.unit f.fractionalBits left right≤1048576*M
  unfold GeneralPaperDyadicMultiplyPrice.width
  change binaryWordWidth left.exponent.natAbs≤256*M at hL
  change binaryWordWidth right.exponent.natAbs≤256*M at hR
  change binaryWordWidth f.unit≤1+2*f.fractionalBits at hUnit
  omega

theorem scaled_exponent (lambda k factor : ℕ) (x : Number)
    (h : x.exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k) :
    (GeneralPaperDyadicCompare.scale factor x).exponent.natAbs≤GeneralPaperQuantileExponentRange.cap lambda k := h

end Blotto.GeneralPaperStoredExponentEnvelope
