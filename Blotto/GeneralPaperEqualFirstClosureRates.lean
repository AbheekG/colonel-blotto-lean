import Blotto.GeneralPaperFirstRealAlgorithmContract

/-! All measured cache phases at the paper first-rounding source size.
The actual closure executes midpoint k+5, independent of the successor
used to bound segment heights. Final budget and address construction are
included; no native cache cost premise is supplied. -/
namespace Blotto.GeneralPaperEqualFirstClosureRates
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  let q := binaryWordWidth n+k+11
  let L := 3670016*q+1
  1048576*(model.rat (1048576*q+1)+A+1) +
    1048576*(model.rat (3670016*q+2)+A+1) +
    (64*(binaryWordWidth (k+5)+1)*(A+model.rat (GeneralPaperNatPowerOperands.width 2 (k+5)))+128*A+128) +
    128*(L+1)*(A+model.rat (L+6)+1) +
    8192*(L+1)*(model.rat (L+8)+A+1) +
    4096*(b+A+model.rat (8*(binaryWordWidth n+binaryWordWidth k+binaryWordWidth b+66))+1)

theorem work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (routes : PreparedGroupOutput (terminal (rounded true model W k values v hv) small).partition)
    (full : PreparedSegmentDescriptor (lottery (rounded true model W k values v hv) small))
    (groupSize : ℕ) (hGroupSize : groupSize = (terminal (rounded true model W k values v hv) small).groups.length)
    (budget : ℚ) :
    let result := (GeneralPaperEqualAddressedClosure.run routes full groupSize hGroupSize model A k budget).2
    let w := result.1
    w.compaction+(w.integerProduct+w.integerCounts)+w.midpointPower+w.rejectionWidth+w.booleanCache+
      (result.2.1+result.2.2.1+result.2.2.2) ≤ bound model A n k (rationalWordWidth budget) := by
  let q := binaryWordWidth n+k+11
  let s := GeneralPaperEqualNativeSampler.segmentHeight n (k+1)
  have hs : 2 ≤ s := by
    dsimp [s, GeneralPaperEqualNativeSampler.segmentHeight, GeneralPaperEqualNativeSampler.fieldHeight, expressionHeightBudget]
    omega
  have hl := GeneralPaperEqualFirstHeights.lottery_height true model W k values v hv small
  have hSize : s ≤ 524288*q := by
    have h := GeneralPaperEqualNativeCache.segment_height_bound n (k+1)
    dsimp [s,q] at *
    omega
  have hCount := (GeneralPaperEqualNativeCache.compact_count (rounded true model W k values v hv) small).2
  have hc := (GeneralPaperEqualCompactedCost.compaction routes full model A (k+5) budget hs hl.1).trans
    (GeneralPaperPreparedSegmentCompaction.headline model A s)
  have hcPrice := model.monotone (show 1+2*s ≤ 1048576*q+1 by omega)
  have hc' : (GeneralPaperEqualCompactedCache.run routes full model A (k+5) budget).2.1 ≤
      1048576*(model.rat (1048576*q+1)+A+1) :=
    hc.trans (Nat.mul_le_mul_left 1048576 (by omega))
  have hi := GeneralPaperEqualCompactedCost.integer routes full model A (k+5) budget hl.1
  have hiHead := GeneralPaperEqualCompactedCost.integer_headline model A _ s hCount
  have hiPrice := model.monotone (show 7*s+2 ≤ 3670016*q+2 by omega)
  have hi' : (GeneralPaperEqualCompactedCache.run routes full model A (k+5) budget).2.2.1+
      (GeneralPaperEqualCompactedCache.run routes full model A (k+5) budget).2.2.2.1 ≤
      1048576*(model.rat (3670016*q+2)+A+1) :=
    ((Nat.add_le_add hi.1 hi.2).trans hiHead).trans (Nat.mul_le_mul_left 1048576 (by omega))
  have hp := GeneralPaperEqualCompactedCost.power routes full model A (k+5) budget
  let p := GeneralPaperEqualPreparedCache.prepare
    (terminal (rounded true model W k values v hv) small).partition
    (lottery (rounded true model W k values v hv) small) (k+5) budget
  have hD := GeneralPaperEqualFirstHeights.categorical_denominator true model W k values v hv small p
  have hR := GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small p
  have hw := GeneralPaperEqualMeasuredClosure.width_work routes full groupSize hGroupSize model A k budget
    (3670016*q+1) hD
  have hb := (GeneralPaperEqualMeasuredClosure.boolean_work routes full groupSize hGroupSize model A k budget
    (3670016*q+1) hD).trans
      (GeneralPaperStoredBooleanCache.headline model A _ _ _ hCount hR)
  have hFinal := GeneralPaperEqualAddressedClosure.closure_work routes full groupSize hGroupSize model A k budget
  have hm := GeneralPaperEqualNativeCache.group_count (rounded true model W k values v hv) small
  have hWord := binaryWordWidth_mono hm
  have h3 : binaryWordWidth 3 = 2 := by decide
  have hArg : GeneralPaperEqualAddressConstruction.operandWidth n
      (terminal (rounded true model W k values v hv) small).groups.length k (rationalWordWidth budget) ≤
      8*(binaryWordWidth n+binaryWordWidth k+binaryWordWidth (rationalWordWidth budget)+66) := by
    unfold GeneralPaperEqualAddressConstruction.operandWidth
    omega
  have hRat := model.monotone hArg
  have hFinal' := hFinal.trans (Nat.mul_le_mul_left 4096 (show
      rationalWordWidth budget+A+model.rat
        (GeneralPaperEqualAddressConstruction.operandWidth n
          (terminal (rounded true model W k values v hv) small).groups.length k (rationalWordWidth budget))+1 ≤
      rationalWordWidth budget+A+model.rat
        (8*(binaryWordWidth n+binaryWordWidth k+binaryWordWidth (rationalWordWidth budget)+66))+1 by omega))
  dsimp only at hFinal' ⊢
  unfold bound
  dsimp only
  change _ ≤ 1048576*(model.rat (1048576*q+1)+A+1)+
    1048576*(model.rat (3670016*q+2)+A+1)+
    (64*(binaryWordWidth (k+5)+1)*(A+model.rat (GeneralPaperNatPowerOperands.width 2 (k+5)))+128*A+128)+
    128*(3670016*q+1+1)*(A+model.rat (3670016*q+1+6)+1)+
    8192*(3670016*q+1+1)*(model.rat (3670016*q+1+8)+A+1)+
    4096*(rationalWordWidth budget+A+model.rat
      (8*(binaryWordWidth n+binaryWordWidth k+binaryWordWidth (rationalWordWidth budget)+66))+1)
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hc' hi') hp) hw) hb) hFinal'

end Blotto.GeneralPaperEqualFirstClosureRates
