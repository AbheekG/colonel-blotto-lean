import Blotto.GeneralPaperEpochNumeratorArrayPrice
import Blotto.GeneralPaperEpochPrefixPrice

/-! Native mantissas bound every local integer numerator and running sum.
The retained summary size and precision derive the encoded total word.
These are erased invariants, without an executed sum or validation pass.
-/
namespace Blotto.GeneralPaperEpochNumeratorEnvelope
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem total_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth ((GeneralPaperSourceParameters.prepare k).summarySize*
      (4*(GeneralPaperPowerPrecision.prepare lambda k).unit))≤
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  change f.fractionalBits≤128*M at hp
  have hu := GeneralPaperParameterOperandBounds.dyadic_word f.fractionalBits
  rw [(GeneralPaperScoreScaleParameters.power_data f.fractionalBits).1,←GeneralPaperPowerPrecision.unit_power lambda k] at hu
  change binaryWordWidth f.unit≤1+2*f.fractionalBits at hu
  have hs := GeneralPaperNatPowerOperands.power_width 2 (34+k)
  have hTwo : binaryWordWidth 2=2 := by decide
  rw [hTwo,←(GeneralPaperSourceParameters.data k).2.2.2.2.2] at hs
  change binaryWordWidth s≤1+(34+k)*2 at hs
  have h4 := binaryWordWidth_mul 4 f.unit
  have hMul := binaryWordWidth_mul s (4*f.unit)
  have hFour : binaryWordWidth 4=3 := by decide
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change k+128≤M at hk
  change 128≤M at hM
  change 1+binaryWordWidth (s*(4*f.unit))≤1048576*M
  omega

theorem returned_total (bits : Bool) (index price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : GeneralPaperUnsignedCellConstancy.Summary k)
    (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    (GeneralPaperEpochNumeratorArrayPrice.run bits index price W c levels).1.data.toList.sum≤
      (GeneralPaperSourceParameters.prepare k).summarySize*(4*c.powers.format.unit) :=
  GeneralPaperEpochPrefixPrice.array_sum_bound _ _
    (GeneralPaperEpochNumeratorArrayPrice.returned_bound bits index price W m lambda k Qv c hc levels hLevels)

theorem returned_total_word (bits : Bool) (index price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (levels : GeneralPaperUnsignedCellConstancy.Summary k)
    (hLevels : ∀ r,levels.read r≤c.controls.precision.levelBound) :
    1+binaryWordWidth (GeneralPaperEpochNumeratorArrayPrice.run bits index price W c levels).1.data.toList.sum≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have h := Nat.add_le_add_left (binaryWordWidth_mono (returned_total bits index price W m lambda k Qv c hc levels hLevels)) 1
  apply h.trans
  rw [hc]
  exact total_word m lambda k Qv

end Blotto.GeneralPaperEpochNumeratorEnvelope
