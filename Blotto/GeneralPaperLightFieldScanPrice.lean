import Blotto.GeneralPaperLightFieldScan

/-! Actual prefix totals bound the classifier's addition operands. No
value-height oracle or original-rational sum is executed. The classification
scan has linear real work and short-integer fast-bit work, including all
literal comparisons, products, additions and reference/index controls. -/
namespace Blotto.GeneralPaperLightFieldScanPrice
open GeneralPaperLightFieldScan GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def magnitude (r Q : ℕ) : ℕ := (r+1)*(Q+1)

theorem prefix_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    (scan bits model W r Q weights count hc).1.lightWeight≤Q := by
  have h := GeneralPaperValueWeightSum.prefix_mono bits model W weights count n hc le_rfl
  rw [GeneralPaperValueWeightSum.total,hs] at h
  exact (light_weight_le bits model W r Q weights count hc).trans h

theorem addition_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count+1≤n) :
    (scan bits model W r Q weights count (by omega)).1.lightWeight+weights.read ⟨count,by omega⟩≤Q := by
  have h := light_weight_le bits model W r Q weights count (by omega)
  have hNext := GeneralPaperValueWeightSum.prefix_mono bits model W weights (count+1) n hc le_rfl
  rw [GeneralPaperValueWeightSum.total,hs,GeneralPaperValueWeightSum.scan] at hNext
  exact (Nat.add_le_add_right h _).trans hNext

theorem bit_work {n : ℕ} (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) (count : ℕ) (hc : count≤n) :
    (scan true model W r Q weights count hc).2≤
      count*(5*model.rat (1+binaryWordWidth (magnitude r Q))+128*arrayWord W n)+64*arrayWord W n := by
  have hA := GeneralPaperSummaryArrayControls.array_word_positive W n
  have hQ : Q≤magnitude r Q := by unfold magnitude; nlinarith
  have hr : r≤magnitude r Q := by unfold magnitude; nlinarith
  induction count with
  | zero => simp only [scan,address,ite_true,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    have hw : weights.read ⟨count,by omega⟩≤Q := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)).trans_eq hs
    have hProduct : r*weights.read ⟨count,by omega⟩≤magnitude r Q := by
      have h := Nat.mul_le_mul_left r hw
      unfold magnitude
      nlinarith only [h]
    have hOld := prefix_bound true model W r Q weights hs count (by omega)
    have hSum := addition_bound true model W r Q weights hs count hc
    have hMul := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b)
      r (weights.read ⟨count,by omega⟩) (magnitude r Q) hr (hw.trans hQ) hProduct
    have hCompare := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone
      (r*weights.read ⟨count,by omega⟩) Q (1+binaryWordWidth (magnitude r Q))
      (Nat.add_le_add_left (binaryWordWidth_mono hProduct) 1) (Nat.add_le_add_left (binaryWordWidth_mono hQ) 1)
    have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b)
      (scan true model W r Q weights count (by omega)).1.lightWeight (weights.read ⟨count,by omega⟩)
      (magnitude r Q) (hOld.trans hQ) (hw.trans hQ) (hSum.trans hQ)
    have hi := GeneralPaperSummaryArrayControls.array_index W n count (by omega)
    have hPrev := ih (by omega)
    rw [scan]
    simp only [address,index,ite_true,PaperIndexedArrayConstruction.stepWork]
    split_ifs <;> nlinarith only [hPrev,hMul,hCompare,hAdd,hi,hA]

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : (scan false model 1 r Q weights count hc).2≤130*count+64 := by
  induction count with
  | zero => simp only [scan,address,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.zero_add,Nat.mul_one,le_refl]
  | succ count ih =>
    have h := ih (by omega)
    rw [scan]
    simp only [address,index,Bool.false_eq_true,ite_false,GeneralPaperNaturalPrimitivePrice.binary,
      GeneralPaperIntegerWordPrice.compare,PaperIndexedArrayConstruction.stepWork,Nat.mul_one]
    split_ifs <;> nlinarith only [h]

end Blotto.GeneralPaperLightFieldScanPrice
