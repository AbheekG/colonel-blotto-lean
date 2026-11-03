import Blotto.GeneralPaperThreeSegmentPreparation

/-! The two-group complementary segment uses the same eager array compiler.
All nine slots, including padded zero slots, are stored and priced. -/
namespace Blotto.GeneralPaperPairSegmentPreparation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1400000
abbrev Expr := RationalExpression 1

def lottery (B : ℚ) := (rationalComplementaryPair B).padRight 8 0
def weight (slot : Fin 9) : Expr := .literal (if slot.val = 0 then 1 else 0)
def left (_slot : Fin 9) (j : Fin 2) : Expr := ![.literal 0, .input 0] j
def right (_slot : Fin 9) (j : Fin 2) : Expr := ![.input 0, .literal 0] j

def environment (B : ℚ) (A : ℕ) : FixedArrayTable 1 ℚ × ℕ :=
  PaperIndexedArrayConstruction.run id A (fun _ => (B, rationalWordWidth B + 32 * A + 32))

theorem environment_data (B : ℚ) (A : ℕ) : (environment B A).1 = FixedArrayTable.ofFn (fun _ : Fin 1 => B) := by
  rw [environment, PaperIndexedArrayConstruction.run_data]

def programs (B : ℚ) (env : FixedArrayTable 1 ℚ) (h : ∀ j, env.read j = B) :
    GeneralPaperSegmentExpressionCompiler.Programs (lottery B) env where
  weight := weight
  left := left
  right := right
  weight_correct := by intro slot; fin_cases slot <;> rfl
  left_correct := by
    intro slot j
    fin_cases slot <;> fin_cases j <;> simp [left, RationalExpression.run, h, lottery,
      RationalSegmentLottery.padRight, rationalComplementaryPair, Fin.addCases]
  right_correct := by
    intro slot j
    fin_cases slot <;> fin_cases j <;> simp [right, RationalExpression.run, h, lottery,
      RationalSegmentLottery.padRight, rationalComplementaryPair, Fin.addCases]

def run (B : ℚ) (model : RationalCostModel) (A : ℕ) : PreparedSegmentDescriptor (lottery B) × ℕ :=
  let env := environment B A
  let h : ∀ j, env.1.read j = B := by intro j; rw [environment_data, FixedArrayTable.read_ofFn]
  let actual := GeneralPaperSegmentExpressionCompiler.run model A env.1 (programs B env.1 h)
  (actual.1, env.2 + actual.2 + 64 * A + 64)

theorem data (B : ℚ) (model : RationalCostModel) (A : ℕ) :
    (run B model A).1 = PreparedSegmentDescriptor.prepare (lottery B) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

theorem weight_work (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 1 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (slot : Fin 9) :
    (GeneralPaperExpressionBitExecution.run model A env (weight slot)).2 ≤
      GeneralPaperExpressionBitExecution.nodeBound model A 1 s := by
  have hq : RationalHeight (if slot.val = 0 then (1 : ℚ) else 0) s := by
    split_ifs <;> exact (show RationalHeight (_ : ℚ) 2 by norm_num [RationalHeight]).mono hs
  simpa only [weight, GeneralPaperExpressionBitExecution.run, env.size] using
    GeneralPaperExpressionBitExecution.leaf_bound model A 1 s _ hq

theorem endpoint_work (model : RationalCostModel) (A : ℕ) (env : FixedArrayTable 1 ℚ) (s : ℕ)
    (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight (env.read j) s) (slot : Fin 9) (j : Fin 2) :
    (GeneralPaperExpressionBitExecution.run model A env (left slot j)).2 ≤ GeneralPaperExpressionBitExecution.nodeBound model A 1 s ∧
    (GeneralPaperExpressionBitExecution.run model A env (right slot j)).2 ≤ GeneralPaperExpressionBitExecution.nodeBound model A 1 s := by
  have hz := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  have hc0 := GeneralPaperExpressionBitExecution.leaf_bound model A 1 s 0 hz
  have hcB := GeneralPaperExpressionBitExecution.leaf_bound model A 1 s (env.read 0) (hEnv 0)
  fin_cases j
  · constructor
    · change rationalWordWidth 0 + GeneralPaperExpressionBitExecution.unit A env.data.size ≤ _
      simpa only [env.size] using hc0
    · change rationalWordWidth (env.read 0) + GeneralPaperExpressionBitExecution.unit A env.data.size ≤ _
      simpa only [env.size] using hcB
  · constructor
    · change rationalWordWidth (env.read 0) + GeneralPaperExpressionBitExecution.unit A env.data.size ≤ _
      simpa only [env.size] using hcB
    · change rationalWordWidth 0 + GeneralPaperExpressionBitExecution.unit A env.data.size ≤ _
      simpa only [env.size] using hc0

def bound (model : RationalCostModel) (A s : ℕ) : ℕ :=
  GeneralPaperSegmentExpressionCompiler.bound A 2 9 (GeneralPaperExpressionBitExecution.nodeBound model A 1 s) +
    (1 + 2 * s + 32 * A + 32) + PaperIndexedArrayConstruction.overhead id A 1 1 + 64 * A + 64

theorem work (B : ℚ) (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (hB : RationalHeight B s) :
    (run B model A).2 ≤ bound model A s := by
  have hEnv : ∀ j, RationalHeight ((environment B A).1.read j) s := by
    intro j
    rw [environment_data, FixedArrayTable.read_ofFn]
    exact hB
  have hInputs : (environment B A).2 ≤ (1 + 2 * s + 32 * A + 32) + PaperIndexedArrayConstruction.overhead id A 1 1 := by
    rw [environment, PaperIndexedArrayConstruction.run_work]
    have h := rationalWordWidth_of_height hB
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Nat.one_mul]
    omega
  have hCompile := GeneralPaperSegmentExpressionCompiler.work model A (environment B A).1
    (programs B (environment B A).1 (fun j => by rw [environment_data, FixedArrayTable.read_ofFn]))
    (GeneralPaperExpressionBitExecution.nodeBound model A 1 s) (weight_work model A _ s hs)
    (fun slot j => (endpoint_work model A _ s hs hEnv slot j).1)
    (fun slot j => (endpoint_work model A _ s hs hEnv slot j).2)
  change _ ≤ GeneralPaperSegmentExpressionCompiler.bound A 2 9
    (GeneralPaperExpressionBitExecution.nodeBound model A 1 s) at hCompile
  unfold run bound
  dsimp only
  omega

theorem headline (model : RationalCostModel) (A s : ℕ) :
    bound model A s ≤ 1073741824 * (model.rat (1 + 2 * expressionHeightBudget s 20) + A + 1) := by
  have h9 := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A 9 9 le_rfl
  have h2 := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A 2 2 le_rfl
  have h1 := PaperIndexedArrayConstruction.overhead_bound id 1 (fun w => by change w ≤ 1 * w; omega) A 1 1 le_rfl
  have h10 : binaryWordWidth 10 = 4 := by decide
  have h3 : binaryWordWidth 3 = 2 := by decide
  have hW2 : binaryWordWidth 2 = 2 := by decide
  rw [h10] at h9
  rw [h3] at h2
  rw [hW2] at h1
  have hs := expressionHeightBudget_ge_input s 20
  have hRat := model.monotone (show 1 + 2 * s ≤ 1 + 2 * expressionHeightBudget s 20 by omega)
  have hS := (show 1 + 2 * s ≤ 1 + 2 * expressionHeightBudget s 20 by omega).trans (model.word_le _)
  unfold bound GeneralPaperSegmentExpressionCompiler.bound GeneralPaperExpressionBitExecution.nodeBound
    GeneralPaperExpressionBitExecution.unit
  rw [hW2]
  nlinarith only [h9, h2, h1, hRat, hS]

end Blotto.GeneralPaperPairSegmentPreparation
