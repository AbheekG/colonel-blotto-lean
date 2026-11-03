import Blotto.GeneralPaperResponsePhysicalHeights

/-! The existing native row checker can use a proved bound for its actual
sum prefixes. Shared-shift response arguments discharge these premises;
no prefix bound or height oracle is added to the executable checker. -/
namespace Blotto.GeneralPaperRowBudgetRefinedPrice
open GeneralPaperRowBudgetExecution
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem scan_work {m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W L : ℕ)
    (row : FixedArrayTable m ℚ) (hItem : ∀ j,rationalWordWidth (row.read j)≤L)
    (hPrefix : ∀ count (hc : count≤m),rationalWordWidth (scan model.rat index W row count hc).1.1≤L)
    (hZero : rationalWordWidth (0:ℚ)≤L) (hW : 1≤W)
    (hi : ∀ i≤m,index (binaryWordWidth (i+1))≤W) (count : ℕ) (hc : count≤m) :
    (scan model.rat index W row count hc).2≤(3*count+1)*model.rat L+(96*count+32)*W := by
  have hz := model.monotone hZero
  induction count with
  | zero => simp only [scan,Nat.mul_zero,Nat.zero_add,Nat.one_mul]; omega
  | succ k ih =>
    let old := scan model.rat index W row k (by omega)
    let q := row.read ⟨k,by omega⟩
    have hOld : rationalWordWidth old.1.1≤L := hPrefix k (by omega)
    have hq : rationalWordWidth q≤L := hItem _
    have hNew : rationalWordWidth (old.1.1+q)≤L := hPrefix (k+1) hc
    have hadd := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone
      (fun a b => a+b) old.1.1 q L hOld hq hNew
    have htest := model.monotone (max_le hq hZero)
    have hIndex := hi k (by omega)
    have hEarlier := ih (by omega)
    rw [scan]
    dsimp only
    change old.2+GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a+b) old.1.1 q+
      model.rat (RationalExpression.pairWidth q 0)+PaperIndexedArrayConstruction.stepWork index W k+32*W≤_
    unfold RationalExpression.pairWidth PaperIndexedArrayConstruction.stepWork
    nlinarith only [hEarlier,hadd,htest,hIndex,hW]

theorem work {m : ℕ} (model : RationalCostModel) (index : ℕ → ℕ) (W L : ℕ)
    (row : FixedArrayTable m ℚ) (B : ℚ) (hItem : ∀ j,rationalWordWidth (row.read j)≤L)
    (hPrefix : ∀ count (hc : count≤m),rationalWordWidth (scan model.rat index W row count hc).1.1≤L)
    (hZero : rationalWordWidth (0:ℚ)≤L) (hB : rationalWordWidth B≤L) (hW : 1≤W)
    (hi : ∀ i≤m,index (binaryWordWidth (i+1))≤W) :
    (run model.rat index W row B).2≤(3*m+2)*model.rat L+128*(m+1)*W := by
  have hs := scan_work model index W L row hItem hPrefix hZero hW hi m le_rfl
  have hp := model.monotone (max_le (hPrefix m le_rfl) hB)
  unfold run RationalExpression.pairWidth
  dsimp only
  nlinarith only [hs,hp]

end Blotto.GeneralPaperRowBudgetRefinedPrice
