import Blotto.GeneralPaperRootScanExecution

/-! Root feasibility compares the exact resource tag to the literal budget
tag. Budget rational words remain explicit; no budget quantization or
unjustified short-input promise is inserted by this price. -/
namespace Blotto.GeneralPaperRootEligiblePrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ) (table : Table Tag Witness J) (budget : Tag) (i : Fin J) : Option (Fin J) × ℕ :=
  match table.read i with
  | none => (none,64*W+64*A)
  | some chosen =>
    let compared := GeneralPaperTagPrimitivePrice.le price W chosen.cost budget
    (if compared.1 then some i else none,compared.2+64*W+64*A)

theorem data {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (W A : ℕ) (table : Table Tag Witness J) (budget : Tag) (i : Fin J) :
    (run price W A table budget i).1=GeneralPaperOrderedProfitRoot.eligible table budget i := by
  cases hr : table.read i with
  | none => simp only [run,hr,GeneralPaperOrderedProfitRoot.eligible]
  | some chosen =>
    simp only [run,hr,GeneralPaperOrderedProfitRoot.eligible,GeneralPaperTagPrimitivePrice.le_data]
    by_cases h : chosen.cost≤budget <;> simp only [h,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]

theorem work {Witness : Type*} {J : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W A s : ℕ)
    (table : Table Tag Witness J) (budget : Tag) (i : Fin J) (ht : GeneralPaperOrderedTableHeight.Safe s table) :
    (run price W A table budget i).2≤2*price (max (1+2*s) (rationalWordWidth budget.threshold))+128*W+64*A := by
  cases hr : table.read i with
  | none => simp only [run,hr]; omega
  | some chosen =>
    have h := GeneralPaperTagPrimitivePrice.le_work price hMono W _ chosen.cost budget
      ((rationalWordWidth_of_height (ht i chosen hr)).trans (le_max_left _ _)) (le_max_right _ _)
    simp only [run,hr]
    omega

theorem arithmetic_work {Witness : Type*} {J : ℕ} (table : Table Tag Witness J) (budget : Tag) (i : Fin J) :
    (run (fun _ => 1) 1 1 table budget i).2≤194 := by
  cases hr : table.read i with
  | none => simp only [run,hr]; omega
  | some chosen => simp only [run,hr,GeneralPaperTagPrimitivePrice.le_arithmetic]; omega

end Blotto.GeneralPaperRootEligiblePrice
