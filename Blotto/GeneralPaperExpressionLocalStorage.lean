import Blotto.GeneralPaperExpressionStorageBudget

/-! The local activation envelope follows each executed evaluator case.
Arithmetic and comparison scratch are their own primitive charges. All
current operand/result values are reserved while recursive children execute;
this conservative overlap avoids relying on reclamation within an expression. -/
namespace Blotto.GeneralPaperExpressionLocalStorage
open GeneralPaperExpressionBitExecution (run)
open GeneralPaperExpressionStorageBudget
set_option autoImplicit false
set_option maxHeartbeats 1400000

def localFoot {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) : RationalExpression k → ℕ
  | .input j => frameEnvelope A env.data.size (run model A env (.input j)).2 + rationalWordWidth (env.read j)
  | .literal q => frameEnvelope A env.data.size (run model A env (.literal q)).2 + rationalWordWidth q
  | .add a b => frameEnvelope A env.data.size (run model A env (.add a b)).2 +
      scalarFrame model A .add (run model A env a).1 (run model A env b).1
  | .sub a b => frameEnvelope A env.data.size (run model A env (.sub a b)).2 +
      scalarFrame model A .sub (run model A env a).1 (run model A env b).1
  | .mul a b => frameEnvelope A env.data.size (run model A env (.mul a b)).2 +
      scalarFrame model A .mul (run model A env a).1 (run model A env b).1
  | .div a b => frameEnvelope A env.data.size (run model A env (.div a b)).2 +
      scalarFrame model A .div (run model A env a).1 (run model A env b).1
  | .minimum a b => frameEnvelope A env.data.size (run model A env (.minimum a b)).2 +
      compareFrame model A (run model A env a).1 (run model A env b).1 + rationalWordWidth (run model A env (.minimum a b)).1
  | .maximum a b => frameEnvelope A env.data.size (run model A env (.maximum a b)).2 +
      compareFrame model A (run model A env a).1 (run model A env b).1 + rationalWordWidth (run model A env (.maximum a b)).1
  | .ifLe a b yes no => frameEnvelope A env.data.size (run model A env (.ifLe a b yes no)).2 +
      compareFrame model A (run model A env a).1 (run model A env b).1 + rationalWordWidth (run model A env (.ifLe a b yes no)).1

theorem bound {k : ℕ} (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable k ℚ) (e : RationalExpression k) :
    localFoot model A env e ≤ 2048 * (run model A env e).2 := by
  have hFrame := frame_bound A env.data.size (run model A env e).2 (unit_le model A env e)
  have hWord := written model A env e
  cases e with
  | input j => simp only [localFoot]; exact (Nat.add_le_add hFrame hWord).trans (by omega)
  | literal q => simp only [localFoot]; exact (Nat.add_le_add hFrame hWord).trans (by omega)
  | add a b =>
    have hScalar := scalar_frame_bound model A .add (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperRationalScalarStep.run model A .add (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.add a b)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega
  | sub a b =>
    have hScalar := scalar_frame_bound model A .sub (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperRationalScalarStep.run model A .sub (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.sub a b)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega
  | mul a b =>
    have hScalar := scalar_frame_bound model A .mul (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperRationalScalarStep.run model A .mul (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.mul a b)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega
  | div a b =>
    have hScalar := scalar_frame_bound model A .div (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperRationalScalarStep.run model A .div (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.div a b)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega
  | minimum a b =>
    have hCompare := compare_frame_bound model A (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperExpressionBitExecution.compare model A (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.minimum a b)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega
  | maximum a b =>
    have hCompare := compare_frame_bound model A (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperExpressionBitExecution.compare model A (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.maximum a b)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega
  | ifLe a b yes no =>
    have hCompare := compare_frame_bound model A (run model A env a).1 (run model A env b).1
    have hOwn : (GeneralPaperExpressionBitExecution.compare model A (run model A env a).1 (run model A env b).1).2 ≤
        (run model A env (.ifLe a b yes no)).2 := by rw [run]; dsimp only; omega
    simp only [localFoot]
    omega

end Blotto.GeneralPaperExpressionLocalStorage
