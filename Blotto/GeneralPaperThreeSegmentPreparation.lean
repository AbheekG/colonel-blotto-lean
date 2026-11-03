import Blotto.GeneralPaperSegmentExpressionCompiler

/-! Actual constant-size three-input segment preparation: one materialized
five-word environment and one fused evaluation per stored weight/endpoint.
Its complete bit observer includes environment, expression and array control. -/
namespace Blotto.GeneralPaperThreeSegmentPreparation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

def environment (i : RationalThreeSpec) (A : ℕ) : FixedArrayTable 5 ℚ × ℕ :=
  PaperIndexedArrayConstruction.run id A (fun j =>
    let value := ![i.B, i.a, i.d, i.c, i.p] j
    (value, rationalWordWidth value + 32 * A + 32))

theorem environment_data (i : RationalThreeSpec) (A : ℕ) :
    (environment i A).1 = RationalThreeSpecCode.environment i := by
  rw [environment, PaperIndexedArrayConstruction.run_data]
  rfl

def programs (i : RationalThreeSpec) (env : FixedArrayTable 5 ℚ) (h : env = RationalThreeSpecCode.environment i) :
    GeneralPaperSegmentExpressionCompiler.Programs i.segmentLottery env where
  weight := GeneralPaperThreeStaticPrograms.orderedWeight
  left := GeneralPaperThreeStaticPrograms.left
  right := GeneralPaperThreeStaticPrograms.right
  weight_correct := by intro slot; rw [h]; exact GeneralPaperThreeStaticPrograms.weight_value i slot
  left_correct := by intro slot j; rw [h]; exact GeneralPaperThreeStaticPrograms.left_value i slot j
  right_correct := by intro slot j; rw [h]; exact GeneralPaperThreeStaticPrograms.right_value i slot j

def run (i : RationalThreeSpec) (model : RationalCostModel) (A : ℕ) : PreparedSegmentDescriptor i.segmentLottery × ℕ :=
  let env := environment i A
  let actual := GeneralPaperSegmentExpressionCompiler.run model A env.1 (programs i env.1 (environment_data i A))
  (actual.1, env.2 + actual.2 + 64 * A + 64)

theorem data (i : RationalThreeSpec) (model : RationalCostModel) (A : ℕ) :
    (run i model A).1 = PreparedSegmentDescriptor.prepare i.segmentLottery := by
  unfold run
  dsimp only
  exact GeneralPaperSegmentExpressionCompiler.data model A (environment i A).1
    (programs i (environment i A).1 (environment_data i A))

theorem weight_work (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 5 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) :
    (GeneralPaperExpressionBitExecution.run model A env (GeneralPaperThreeStaticPrograms.orderedWeight slot)).2 ≤
      2048 * GeneralPaperExpressionBitExecution.nodeBound model A 5 (expressionHeightBudget s 20) :=
  GeneralPaperExpressionBitExecution.work_height model A env _ s 20 2048 hEnv
    (RationalExpression.LiteralHeights_mono _ hs (GeneralPaperThreeStaticPrograms.weight_literals slot))
    (GeneralPaperThreeStaticPrograms.weight_depth slot) (GeneralPaperThreeStaticPrograms.weight_operations slot)

theorem left_work (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 5 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) (j : Fin 3) :
    (GeneralPaperExpressionBitExecution.run model A env (GeneralPaperThreeStaticPrograms.left slot j)).2 ≤
      2048 * GeneralPaperExpressionBitExecution.nodeBound model A 5 (expressionHeightBudget s 20) :=
  GeneralPaperExpressionBitExecution.work_height model A env _ s 20 2048 hEnv
    (RationalExpression.LiteralHeights_mono _ hs (GeneralPaperThreeStaticPrograms.left_literals slot j))
    (GeneralPaperThreeStaticPrograms.left_depth slot j) (GeneralPaperThreeStaticPrograms.left_operations slot j)

theorem right_work (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 5 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) (j : Fin 3) :
    (GeneralPaperExpressionBitExecution.run model A env (GeneralPaperThreeStaticPrograms.right slot j)).2 ≤
      2048 * GeneralPaperExpressionBitExecution.nodeBound model A 5 (expressionHeightBudget s 20) :=
  GeneralPaperExpressionBitExecution.work_height model A env _ s 20 2048 hEnv
    (RationalExpression.LiteralHeights_mono _ hs (GeneralPaperThreeStaticPrograms.right_literals slot j))
    (GeneralPaperThreeStaticPrograms.right_depth slot j) (GeneralPaperThreeStaticPrograms.right_operations slot j)

def bound (model : RationalCostModel) (A s : ℕ) : ℕ :=
  GeneralPaperSegmentExpressionCompiler.bound A 3 9
    (2048 * GeneralPaperExpressionBitExecution.nodeBound model A 5 (expressionHeightBudget s 20)) +
    5 * (1 + 2 * s + 32 * A + 32) + PaperIndexedArrayConstruction.overhead id A 5 5 + 64 * A + 64

theorem environment_work (i : RationalThreeSpec) (A s : ℕ)
    (hEnv : ∀ j, RationalHeight ((RationalThreeSpecCode.environment i).read j) s) :
    (environment i A).2 ≤ 5 * (1 + 2 * s + 32 * A + 32) + PaperIndexedArrayConstruction.overhead id A 5 5 := by
  rw [environment, PaperIndexedArrayConstruction.run_work]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    Nat.add_le_add_right (Nat.add_le_add_right (rationalWordWidth_of_height (hEnv j)) (32 * A)) 32)
  simpa only [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using Nat.add_le_add_right h _

theorem work (i : RationalThreeSpec) (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((RationalThreeSpecCode.environment i).read j) s) :
    (run i model A).2 ≤ bound model A s := by
  have he : ∀ j, RationalHeight ((environment i A).1.read j) s := by
    intro j
    rw [environment_data]
    exact hEnv j
  have hCompile := GeneralPaperSegmentExpressionCompiler.work model A (environment i A).1
    (programs i (environment i A).1 (environment_data i A))
    (2048 * GeneralPaperExpressionBitExecution.nodeBound model A 5 (expressionHeightBudget s 20))
    (weight_work model A _ s hs he) (left_work model A _ s hs he) (right_work model A _ s hs he)
  have hInput := environment_work i A s hEnv
  unfold run bound
  dsimp only
  omega

theorem headline (model : RationalCostModel) (A s : ℕ) :
    bound model A s ≤ 1073741824 * (model.rat (1 + 2 * expressionHeightBudget s 20) + A + 1) := by
  have h9 := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A 9 9 le_rfl
  have h3 := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A 3 3 le_rfl
  have h5 := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A 5 5 le_rfl
  have h10 : binaryWordWidth 10 = 4 := by decide
  have h4 : binaryWordWidth 4 = 3 := by decide
  have h6 : binaryWordWidth 6 = 3 := by decide
  rw [h10] at h9
  rw [h4] at h3
  rw [h6] at h5
  have hs := expressionHeightBudget_ge_input s 20
  have hS := (show 1 + 2 * s ≤ 1 + 2 * expressionHeightBudget s 20 by omega).trans (model.word_le _)
  unfold bound GeneralPaperSegmentExpressionCompiler.bound GeneralPaperExpressionBitExecution.nodeBound
    GeneralPaperExpressionBitExecution.unit
  rw [h6]
  nlinarith only [h9, h3, h5, hS]

end Blotto.GeneralPaperThreeSegmentPreparation
