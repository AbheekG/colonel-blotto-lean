import Blotto.GeneralPaperThreeStaticCorrectness

/-! Closed finite syntax checks for fixed programs, not numerical evidence
about a game. Kernel reduction verifies every slot/coordinate program. -/
namespace Blotto.GeneralPaperThreeStaticPrograms
set_option autoImplicit false
set_option maxHeartbeats 2000000

def literalsDecidable {k : ℕ} (s : ℕ) : (e : RationalExpression k) → Decidable (e.LiteralHeights s)
  | .input _ => isTrue trivial
  | .literal q => inferInstanceAs (Decidable (q.num.natAbs < 2 ^ s ∧ q.den < 2 ^ s))
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b =>
    let _ := literalsDecidable s a
    let _ := literalsDecidable s b
    inferInstanceAs (Decidable (a.LiteralHeights s ∧ b.LiteralHeights s))
  | .ifLe a b yes no =>
    let _ := literalsDecidable s a
    let _ := literalsDecidable s b
    let _ := literalsDecidable s yes
    let _ := literalsDecidable s no
    inferInstanceAs (Decidable (a.LiteralHeights s ∧ b.LiteralHeights s ∧ yes.LiteralHeights s ∧ no.LiteralHeights s))

theorem weight_depth (slot : Fin 9) : (orderedWeight slot).depth ≤ 20 := by fin_cases slot <;> decide
theorem weight_operations (slot : Fin 9) : (orderedWeight slot).operationBound ≤ 2048 := by fin_cases slot <;> decide
theorem weight_literals (slot : Fin 9) : (orderedWeight slot).LiteralHeights 2 := by
  let _ := literalsDecidable 2 (orderedWeight slot)
  fin_cases slot <;> decide

theorem left_depth (slot : Fin 9) (j : Fin 3) : (left slot j).depth ≤ 20 := by fin_cases slot <;> fin_cases j <;> decide
theorem left_operations (slot : Fin 9) (j : Fin 3) : (left slot j).operationBound ≤ 2048 := by fin_cases slot <;> fin_cases j <;> decide
theorem left_literals (slot : Fin 9) (j : Fin 3) : (left slot j).LiteralHeights 2 := by
  let _ := literalsDecidable 2 (left slot j)
  fin_cases slot <;> fin_cases j <;> decide

theorem right_depth (slot : Fin 9) (j : Fin 3) : (right slot j).depth ≤ 20 := by fin_cases slot <;> fin_cases j <;> decide
theorem right_operations (slot : Fin 9) (j : Fin 3) : (right slot j).operationBound ≤ 2048 := by fin_cases slot <;> fin_cases j <;> decide
theorem right_literals (slot : Fin 9) (j : Fin 3) : (right slot j).LiteralHeights 2 := by
  let _ := literalsDecidable 2 (right slot j)
  fin_cases slot <;> fin_cases j <;> decide

end Blotto.GeneralPaperThreeStaticPrograms
