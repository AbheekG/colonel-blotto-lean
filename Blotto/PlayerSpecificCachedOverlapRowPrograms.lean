import Blotto.PlayerSpecificCachedOverlapRowExecution

/-! The cached endpoint vectors use the same fixed formula branches;
their original depth/literal bounds do not depend on the cached test. -/
namespace Blotto.PlayerSpecificCachedOverlapRowPrograms
open PlayerSpecificCachedOverlapRowExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem weight_depth (j : Fin 1) : (weightPrograms.read j).depth≤7 := by
  rw [weightPrograms,FixedArrayTable.read_ofFn]
  exact OverlapFormulaCode.weight_depth
theorem weight_literals (j : Fin 1) : (weightPrograms.read j).LiteralHeights 2 := by
  rw [weightPrograms,FixedArrayTable.read_ofFn]
  exact OverlapFormulaCode.weight_literals
theorem first_depth (b : Bool) (j : Fin 4) : ((firstPrograms b).read j).depth≤9 := by
  cases b <;> fin_cases j <;> decide
theorem second_depth (b : Bool) (j : Fin 4) : ((secondPrograms b).read j).depth≤9 := by
  cases b <;> fin_cases j <;> decide
theorem first_literals (b : Bool) (j : Fin 4) : ((firstPrograms b).read j).LiteralHeights 2 := by
  cases b
  · simpa only [firstPrograms,Bool.false_eq_true,ite_false,FixedArrayTable.read_ofFn] using (OverlapFormulaCode.safeP_literals j).2.2.2
  · simpa only [firstPrograms,ite_true,FixedArrayTable.read_ofFn] using (OverlapFormulaCode.safeP_literals j).2.2.1
theorem second_literals (b : Bool) (j : Fin 4) : ((secondPrograms b).read j).LiteralHeights 2 := by
  cases b
  · simpa only [secondPrograms,Bool.false_eq_true,ite_false,FixedArrayTable.read_ofFn] using (OverlapFormulaCode.safeQ_literals j).2.2.2
  · simpa only [secondPrograms,ite_true,FixedArrayTable.read_ofFn] using (OverlapFormulaCode.safeQ_literals j).2.2.1

end Blotto.PlayerSpecificCachedOverlapRowPrograms
