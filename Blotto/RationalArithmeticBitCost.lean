import Blotto.RationalRegisterWidths
import Blotto.RationalExpressionBitCost

/-! Actual operand-sized prices for shared-register rational programs. Each
instruction pays two operand copies, one rational primitive, and a full copy
of its appended register array. This covers conservative scratch copying;
address/control, allocator and physical backend contracts remain separate. -/

namespace Blotto.RationalArithmeticProgram
open scoped BigOperators

def registerCopyCost (registers : Array ℚ) : ℕ :=
  ∑ j : Fin registers.size, rationalWordWidth (registers.getD j.val 0)

theorem registerCopyCost_bound (model : RationalCostModel) (registers : Array ℚ) (W : ℕ)
    (h : WordBounds registers W) : registerCopyCost registers ≤ registers.size * model.rat W := by
  have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin registers.size)))
    (f := fun j => rationalWordWidth (registers.getD j.val 0)) (g := fun _ => model.rat W)
    (fun j _ => (h j.val).trans (model.word_le W))
  have hConst : (∑ _j : Fin registers.size, model.rat W) = registers.size * model.rat W := by simp
  exact hSum.trans_eq hConst

def instructionBitCost (model : RationalCostModel) (instruction : RealArithmeticInstruction)
    (registers : Array ℚ) : ℕ :=
  rationalWordWidth (registers.getD instruction.left 0) +
    rationalWordWidth (registers.getD instruction.right 0) +
    model.rat (RationalExpression.pairWidth (registers.getD instruction.left 0) (registers.getD instruction.right 0)) +
    registerCopyCost (instruction.executeRat registers)

theorem instructionBitCost_bound (model : RationalCostModel) (instruction : RealArithmeticInstruction)
    (registers : Array ℚ) (W : ℕ) (hBefore : WordBounds registers W)
    (hAfter : WordBounds (instruction.executeRat registers) W) :
    instructionBitCost model instruction registers ≤ (3 + (registers.size + 1)) * model.rat W := by
  have hLeft := (hBefore instruction.left).trans (model.word_le W)
  have hRight := (hBefore instruction.right).trans (model.word_le W)
  have hCall := model.monotone (show
    RationalExpression.pairWidth (registers.getD instruction.left 0) (registers.getD instruction.right 0) ≤ W
      from max_le (hBefore instruction.left) (hBefore instruction.right))
  have hCopy := registerCopyCost_bound model (instruction.executeRat registers) W hAfter
  rw [instruction.executeRat_size] at hCopy
  unfold instructionBitCost
  nlinarith

def bitCost (model : RationalCostModel) : List RealArithmeticInstruction → Array ℚ → ℕ
  | [], _ => 0
  | instruction :: rest, registers =>
    instructionBitCost model instruction registers + bitCost model rest (instruction.executeRat registers)

theorem bitCost_bound (model : RationalCostModel) (program : List RealArithmeticInstruction)
    (registers : Array ℚ) (W : ℕ) (hZero : rationalWordWidth (0 : ℚ) ≤ W)
    (hFinal : WordBounds (run program registers) W) :
    bitCost model program registers ≤ RealArithmeticProgram.conservativeWork registers.size program * model.rat W := by
  induction program generalizing registers with
  | nil => simp [bitCost, RealArithmeticProgram.conservativeWork, RealArithmeticProgram.copyAllowance]
  | cons instruction rest ih =>
    have hBefore := hFinal.before_run hZero
    change WordBounds (run rest (instruction.executeRat registers)) W at hFinal
    have hAfter := hFinal.before_run hZero
    have hInstruction := instructionBitCost_bound model instruction registers W hBefore hAfter
    have hRest := ih (instruction.executeRat registers) hFinal
    rw [instruction.executeRat_size] at hRest
    simp only [RealArithmeticProgram.conservativeWork, RealArithmeticProgram.copyAllowance, List.length_cons] at hRest ⊢
    unfold bitCost
    nlinarith

end Blotto.RationalArithmeticProgram
