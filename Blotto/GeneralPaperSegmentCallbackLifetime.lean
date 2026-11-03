import Blotto.GeneralPaperExpressionCallLifetime

/-! Every actual fixed segment-program callback has bounded recursive live
storage. Both control regimes, all sorted/swapped geometries and zero slots
are covered by the checked static syntax and actual fused evaluator. -/
namespace Blotto.GeneralPaperSegmentCallbackLifetime
open GeneralPaperExpressionCallLifetime (live bounded_work)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def threeProfile (model : RationalCostModel) (A s : ℕ) : ℕ :=
  2048 * 2048 * (2048 * GeneralPaperExpressionBitExecution.nodeBound model A 5 (expressionHeightBudget s 20))

theorem three_weight (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 5 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) :
    live model A env (GeneralPaperThreeStaticPrograms.orderedWeight slot) ≤ threeProfile model A s :=
  bounded_work model A env _ 2048 _ (GeneralPaperThreeStaticPrograms.weight_operations slot)
    (GeneralPaperThreeSegmentPreparation.weight_work model A env s hs hEnv slot)

theorem three_left (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 5 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) (j : Fin 3) :
    live model A env (GeneralPaperThreeStaticPrograms.left slot j) ≤ threeProfile model A s :=
  bounded_work model A env _ 2048 _ (GeneralPaperThreeStaticPrograms.left_operations slot j)
    (GeneralPaperThreeSegmentPreparation.left_work model A env s hs hEnv slot j)

theorem three_right (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 5 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) (j : Fin 3) :
    live model A env (GeneralPaperThreeStaticPrograms.right slot j) ≤ threeProfile model A s :=
  bounded_work model A env _ 2048 _ (GeneralPaperThreeStaticPrograms.right_operations slot j)
    (GeneralPaperThreeSegmentPreparation.right_work model A env s hs hEnv slot j)

def pairProfile (model : RationalCostModel) (A s : ℕ) : ℕ :=
  2048 * GeneralPaperExpressionBitExecution.nodeBound model A 1 s

theorem pair_weight (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 1 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (slot : Fin 9) :
    live model A env (GeneralPaperPairSegmentPreparation.weight slot) ≤ pairProfile model A s := by
  have hOps : (GeneralPaperPairSegmentPreparation.weight slot).operationBound ≤ 1 := by rfl
  simpa only [pairProfile, Nat.mul_one, one_mul] using bounded_work model A env _ 1 _ hOps
    (GeneralPaperPairSegmentPreparation.weight_work model A env s hs slot)

theorem pair_endpoints (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 1 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) (j : Fin 2) :
    live model A env (GeneralPaperPairSegmentPreparation.left slot j) ≤ pairProfile model A s ∧
      live model A env (GeneralPaperPairSegmentPreparation.right slot j) ≤ pairProfile model A s := by
  have hLeft : (GeneralPaperPairSegmentPreparation.left slot j).operationBound ≤ 1 := by
    fin_cases j <;> rfl
  have hRight : (GeneralPaperPairSegmentPreparation.right slot j).operationBound ≤ 1 := by
    fin_cases j <;> rfl
  have h := GeneralPaperPairSegmentPreparation.endpoint_work model A env s hs hEnv slot j
  constructor
  · simpa only [pairProfile, Nat.mul_one, one_mul] using bounded_work model A env _ 1 _ hLeft h.1
  · simpa only [pairProfile, Nat.mul_one, one_mul] using bounded_work model A env _ 1 _ hRight h.2

end Blotto.GeneralPaperSegmentCallbackLifetime
