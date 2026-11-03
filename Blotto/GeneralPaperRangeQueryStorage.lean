import Blotto.GeneralPaperRangeTraversalStorage

/-! Range-query frames and primitive scratch share one source-level bound.
The full bit-operation allowance reserves primitive scratch conservatively.
Owned tree payloads are counted by the old/new forest ledger; this module
counts borrowed tree cursors, geometry, controls and native result records. -/
namespace Blotto.GeneralPaperRangeQueryStorage
open GeneralPaperIntervalCache GeneralPaperIntervalLevels
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) : ℕ :=
  GeneralPaperRangeTraversalStorage.peak W c.powers (lo:ℚ) hi amount height n 0 span+
    (1+binaryWordWidth lo)+(1+binaryWordWidth hi)+
    (GeneralPaperRangeRootPrice.run true model.rat W c lo hi amount height n span).2

def profile (model : RationalCostModel) (W m lambda k Qv height : ℕ) : ℕ :=
  (height+1)*(6*GeneralPaperDecoderControls.operandWidth lambda+
    6*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+384*W)+
    2*GeneralPaperDecoderControls.operandWidth lambda+
    (1+4*height)*GeneralPaperRangeUpdateBitPrice.nodeProfile model.rat W m lambda k Qv+
    2*model.rat (GeneralPaperDecoderControls.operandWidth lambda)+64*W

theorem bounded (model : RationalCostModel) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hs : span=(2:ℚ)^height)
    (hh : height≤lambda+1) (hl : lo≤2^(lambda+1)) (hr : hi≤2^(lambda+1))
    (ha : amount≤GeneralPaperPowerPrecision.levelBound lambda k) (hv : Valid lambda k n)
    (hf : ∀ i<2^height,levelAt n i+(if lo ≤ i ∧ i < hi then amount else 0)≤GeneralPaperPowerPrecision.levelBound lambda k) :
    window model W c lo hi amount height n span≤profile model W m lambda k Qv height := by
  have hScratch := GeneralPaperRangeUpdateBitPrice.root_work model.rat model.monotone W m lambda k Qv c hc
    lo hi amount height n span hs hh hl hr hv hf
  have hStack := GeneralPaperRangeTraversalStorage.root W m lambda k Qv lo hi amount height n hh hl hr
  have haW := (Nat.add_le_add_left (binaryWordWidth_mono ha) 1).trans
    (GeneralPaperFreshMassPrice.offset_width m lambda k Qv)
  have hCoeff : GeneralPaperRangeTraversalStorage.coefficient W m lambda k Qv amount≤
      6*GeneralPaperDecoderControls.operandWidth lambda+6*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+384*W := by
    unfold GeneralPaperRangeTraversalStorage.coefficient
    omega
  have hS := hStack.trans (Nat.mul_le_mul_left (height+1) hCoeff)
  have hlW := GeneralPaperRangeGeometryPrice.natural_word lambda lo hl
  have hrW := GeneralPaperRangeGeometryPrice.natural_word lambda hi hr
  have hSum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hS hlW) hrW) hScratch
  unfold window
  have hp : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  rw [hp,hs]
  rw [hs] at hSum
  exact hSum.trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperRangeQueryStorage
