import Blotto.GeneralPaperFiniteAtomicLaw
import Blotto.FareyRationalMembership

/-! Actual closed decoder choices for bounded-denominator rational rows.
The resource identity and closed flags give the exact hard tag budget.
These are proof comparators; no finite alphabet enumeration is executed.
-/
namespace Blotto.GeneralPaperRationalCodeRows
open scoped BigOperators Classical
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem field_exists (a : Alphabet) (r : ℚ) (hr : 0≤r ∧ r≤1) (hDen : r.den≤a.D) :
    ∃ code choice, (decode a false code).choice=some choice ∧ choice.threshold.value=r ∧ choice.opened=false := by
  have hf : (Farey.fractionOfRat r).value=r := Farey.fractionOfRat_value r hr.1
  apply GeneralPaperCodeCoverage.closed_decode a r
  exact Or.inl ⟨Farey.fractionOfRat r,hDen,by rw [hf]; exact hr.1,by rw [hf]; exact hr.2,hf.symm⟩

theorem row_tag_budget {m : ℕ} (B : ℚ) (r : Fin m → ℚ) (choice : Fin m → Choice)
    (hValue : ∀ j, (choice j).threshold.value=r j) (hClosed : ∀ j, (choice j).opened=false)
    (hBudget : ∑ j, r j≤B) : (∑ j, (choice j).tag)≤GeneralPaperResponseTag.budget B := by
  have he : GeneralPaperTagBudgetTransfer.rowTag (fun j => (choice j).threshold) (fun j => (choice j).opened)≤GeneralPaperResponseTag.budget B := by
    rw [GeneralPaperTagBudgetTransfer.tag_budget_iff]
    simp only [hValue,hClosed,implies_true,and_true]
    exact lt_or_eq_of_le hBudget
  simpa only [GeneralPaperTagBudgetTransfer.rowTag,List.sum_ofFn,Choice.tag] using he

theorem physical_value (r : ℚ) (choice : Choice) (hValue : choice.threshold.value=r) (hClosed : choice.opened=false) (delta : ℚ) :
    choice.physical delta=r := by simp only [Choice.physical,hValue,hClosed,Bool.false_eq_true,ite_false,add_zero]

end Blotto.GeneralPaperRationalCodeRows
