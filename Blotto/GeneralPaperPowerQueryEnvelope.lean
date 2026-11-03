import Blotto.GeneralPaperCachedPowerQuery

/-! Both actual query operand sizes and the complete bit price are derived
from the returned source parameter measure. The table/precision/level range
are supplied by their native constructed records, not by width oracles.
-/
namespace Blotto.GeneralPaperPowerQueryEnvelope
open GeneralPaperSourcePreparationSizes GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

theorem width_bound (m lambda k Qv : ℕ) :
    GeneralPaperCachedPowerQuery.operandWidth (GeneralPaperPreparedPowers.prepare lambda k)≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let M := measure m lambda k Qv
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k
  let E := GeneralPaperPowerTableBounds.budget f.fractionalBits f.columns b.number
  let R := f.fractionalBits+f.columns*(E+f.fractionalBits+1)
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have hp := hm.fractionalBits
  have hc := hm.columns
  change f.fractionalBits≤128*M at hp
  change f.columns≤32*M at hc
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change 128≤M at hM
  have hBase : b.number.exponent.natAbs=f.fractionalBits+1 := by
    simp only [b,GeneralPaperStoredGeometricBase.construct,Int.natAbs_neg,Int.natAbs_natCast]
  have hBWord : binaryWordWidth (b.number.exponent.natAbs+f.fractionalBits+1)≤f.fractionalBits+4 := by
    rw [hBase,show f.fractionalBits+1+f.fractionalBits+1=2*(f.fractionalBits+1) by omega]
    have hh := binaryWordWidth_mul 2 (f.fractionalBits+1)
    have hs := GeneralPaperInitializerControlCounters.word_le_self (f.fractionalBits+1)
    have h2 : binaryWordWidth 2=2 := by decide
    omega
  have hD := GeneralPaperNatPowerOperands.power_width 2 f.columns
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at hD
  have hE := GeneralPaperPowerTableBounds.budget_word f.fractionalBits f.columns b.number
  change binaryWordWidth E≤1+2*f.columns+binaryWordWidth (b.number.exponent.natAbs+f.fractionalBits+1) at hE
  have hP := GeneralPaperInitializerControlCounters.word_le_self f.fractionalBits
  have hC := GeneralPaperInitializerControlCounters.word_le_self f.columns
  have hEP := GeneralPaperRayOperandWidthEnvelope.word_add E f.fractionalBits
  have hEP1 := GeneralPaperRayOperandWidthEnvelope.word_add (E+f.fractionalBits) 1
  have hMul := binaryWordWidth_mul f.columns (E+f.fractionalBits+1)
  have hR := GeneralPaperRayOperandWidthEnvelope.word_add f.fractionalBits (f.columns*(E+f.fractionalBits+1))
  have h1 : binaryWordWidth 1=1 := by decide
  change GeneralPaperPowerQueryBounds.width f.fractionalBits f.columns (2^f.columns) R≤1048576*M
  unfold GeneralPaperPowerQueryBounds.width
  dsimp only [R]
  omega

theorem profile_bound (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ) :
    GeneralPaperCachedPowerQuery.profile primitive W (GeneralPaperPreparedPowers.prepare lambda k)≤
      131072*measure m lambda k Qv*(W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have hc := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).columns
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold GeneralPaperCachedPowerQuery.profile
  exact Nat.mul_le_mul
    (show 2048*((GeneralPaperPreparedPowers.prepare lambda k).format.columns+1)≤131072*measure m lambda k Qv by
      change (GeneralPaperPowerPrecision.prepare lambda k).columns≤32*measure m lambda k Qv at hc
      change 2048*((GeneralPaperPowerPrecision.prepare lambda k).columns+1)≤_
      omega)
    (Nat.add_le_add_left (hMono (width_bound m lambda k Qv)) W)

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (exponent : ℕ) (hExponent : exponent≤c.controls.precision.levelBound) :
    (GeneralPaperCachedPowerQuery.query primitive W c exponent).2≤
      131072*measure m lambda k Qv*(W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
  have h := GeneralPaperCachedPowerQuery.work primitive hMono W m lambda k Qv c hc exponent hExponent
  have hp : GeneralPaperCachedPowerQuery.profile primitive W c.powers≤
      131072*measure m lambda k Qv*(W+primitive (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := by
    rw [hc]
    exact profile_bound primitive hMono W m lambda k Qv
  exact h.trans hp

theorem bit_work (model : RationalCostModel) (m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (exponent : ℕ) (hExponent : exponent≤c.controls.precision.levelBound) :
    (GeneralPaperCachedPowerQuery.query model.rat (GeneralPaperSourcePreparationControls.word m lambda k Qv) c exponent).2≤
      262144*measure m lambda k Qv*model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) := by
  have h := work model.rat model.monotone (GeneralPaperSourcePreparationControls.word m lambda k Qv) m lambda k Qv c hc exponent hExponent
  have hw := GeneralPaperSourcePreparationControls.word_le_operand_width m lambda k Qv
  have hWidth : width m lambda k Qv≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    unfold width GeneralPaperPowerPreparationEnvelope.operandWidth
    omega
  have hPrice := (hw.trans hWidth).trans (model.word_le (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv))
  calc
    _ ≤ 131072*measure m lambda k Qv*(GeneralPaperSourcePreparationControls.word m lambda k Qv+
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := h
    _ ≤ 131072*measure m lambda k Qv*(2*model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

end Blotto.GeneralPaperPowerQueryEnvelope
