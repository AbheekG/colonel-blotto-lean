import Blotto.GeneralPaperRootEligiblePrice

/-! One priced native root selection with its actual index-list constructor.
The budget word and retained root-resource height are separate operands. -/
namespace Blotto.GeneralPaperRootSelectPrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {Witness : Type*} {J : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (table : Table Tag Witness J) (budget : Tag) : Option (Fin J) × ℕ :=
  let A := if bits then arrayWord W (J+2) else W
  let labels := GeneralPaperDPTableControls.labels index W A J
  let chosen := GeneralPaperRootScanExecution.run index W (GeneralPaperRootEligiblePrice.run price W A table budget) labels.1
  (chosen.1,labels.2+chosen.2+128*W)

theorem data {Witness : Type*} {J : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (table : Table Tag Witness J) (budget : Tag) :
    (run bits index price W table budget).1=GeneralPaperOrderedProfitRoot.select table budget := by
  unfold run
  dsimp only
  rw [GeneralPaperRootScanExecution.data,GeneralPaperDPTableControls.labels_data]
  have he : (fun i => (GeneralPaperRootEligiblePrice.run price W (if bits then arrayWord W (J+2) else W) table budget i).1)=
      GeneralPaperOrderedProfitRoot.eligible table budget := funext (fun i => GeneralPaperRootEligiblePrice.data price W _ table budget i)
  rw [he]
  rfl

def profile (price : ℕ → ℕ) (W J s budgetWord : ℕ) : ℕ :=
  GeneralPaperDPTableControls.labelsProfile W J+
    J*(2*price (max (1+2*s) budgetWord)+256*W+65*arrayWord W (J+2))+192*W

theorem index_word (W J : ℕ) (i : Fin J) : 1+binaryWordWidth i.val≤arrayWord W (J+2) := by
  have h := binaryWordWidth_mono (show i.val≤(J+2)+1 by have := i.isLt; omega)
  unfold arrayWord
  omega

theorem work {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W s : ℕ)
    (table : Table Tag Witness J) (budget : Tag) (ht : GeneralPaperOrderedTableHeight.Safe s table) :
    (run true (fun x => x) price W table budget).2≤profile price W J s (rationalWordWidth budget.threshold) := by
  let A := arrayWord W (J+2)
  let labels := GeneralPaperDPTableControls.labels (fun x => x) W A J
  have hs := GeneralPaperRootScanExecution.work (fun x => x) W A
    (2*price (max (1+2*s) (rationalWordWidth budget.threshold))+128*W+64*A)
    (GeneralPaperRootEligiblePrice.run price W A table budget) labels.1 (index_word W J)
    (fun i _ => GeneralPaperRootEligiblePrice.work price hMono W A s table budget i ht)
  have hl := GeneralPaperDPTableControls.labels_bit_work W J
  have hLen : labels.1.length=J := by rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hLen] at hs
  change labels.2+(GeneralPaperRootScanExecution.run (fun x => x) W
    (GeneralPaperRootEligiblePrice.run price W A table budget) labels.1).2+128*W≤_
  unfold profile
  dsimp only [A] at hs
  nlinarith only [hs,hl]

theorem arithmetic_work {Witness : Type*} {J : ℕ} (table : Table Tag Witness J) (budget : Tag) :
    (run false (fun _ => 1) (fun _ => 1) 1 table budget).2≤459*J+210 := by
  let labels := GeneralPaperDPTableControls.labels (fun _ => 1) 1 1 J
  have hs := GeneralPaperRootScanExecution.arithmetic_work 194 (GeneralPaperRootEligiblePrice.run (fun _ => 1) 1 1 table budget)
    labels.1 (fun i _ => GeneralPaperRootEligiblePrice.arithmetic_work table budget i)
  have hl := GeneralPaperDPTableControls.labels_arithmetic_work J
  have hLen : labels.1.length=J := by rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hLen] at hs
  change labels.2+(GeneralPaperRootScanExecution.run (fun _ => 1) 1
    (GeneralPaperRootEligiblePrice.run (fun _ => 1) 1 1 table budget) labels.1).2+128≤_
  nlinarith only [hs,hl]

end Blotto.GeneralPaperRootSelectPrice
