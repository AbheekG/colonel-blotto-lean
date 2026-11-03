import Blotto.GeneralPaperSegmentCallbackLifetime

/-! The actual stored group count selects the pair/three callback envelope.
Native rounded fields derive its short-word bound for every stored slot.
Borrowed environment, code and surrounding partial arrays are separate owners. -/
namespace Blotto.GeneralPaperNativeSegmentCallbackStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000

inductive Tag (m : ℕ) where
  | weight (slot : Fin 9)
  | left (slot : Fin 9) (coordinate : Fin m)
  | right (slot : Fin 9) (coordinate : Fin m)

def pairLive {m : ℕ} (i : RationalUniformGroupSpec m) (h2 : m = 2)
    (model : RationalCostModel) (A : ℕ) (tag : Tag m) : ℕ := by
  subst m
  let env := (GeneralPaperPairSegmentPreparation.environment i.B A).1
  cases tag with
  | weight slot => exact GeneralPaperExpressionCallLifetime.live model A env (GeneralPaperPairSegmentPreparation.weight slot)
  | left slot j => exact GeneralPaperExpressionCallLifetime.live model A env (GeneralPaperPairSegmentPreparation.left slot j)
  | right slot j => exact GeneralPaperExpressionCallLifetime.live model A env (GeneralPaperPairSegmentPreparation.right slot j)

def tripleLive {m : ℕ} (i : RationalUniformGroupSpec m) (h3 : m = 3)
    (model : RationalCostModel) (A : ℕ) (tag : Tag m) : ℕ := by
  subst m
  let env := (GeneralPaperThreeSegmentPreparation.environment i.threeInput A).1
  cases tag with
  | weight slot => exact GeneralPaperExpressionCallLifetime.live model A env (GeneralPaperThreeStaticPrograms.orderedWeight slot)
  | left slot j => exact GeneralPaperExpressionCallLifetime.live model A env (GeneralPaperThreeStaticPrograms.left slot j)
  | right slot j => exact GeneralPaperExpressionCallLifetime.live model A env (GeneralPaperThreeStaticPrograms.right slot j)

def live {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A : ℕ) (tag : Tag m) : ℕ :=
  if h2 : size = 2 then pairLive i (hSize.symm.trans h2) model A tag
  else tripleLive i (hm.resolve_left (fun h => h2 (hSize.trans h))) model A tag

def profile (model : RationalCostModel) (A s : ℕ) : ℕ :=
  GeneralPaperSegmentCallbackLifetime.pairProfile model A s + GeneralPaperSegmentCallbackLifetime.threeProfile model A s

theorem pair_bound {m : ℕ} (i : RationalUniformGroupSpec m) (h2 : m = 2)
    (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (tag : Tag m) :
    pairLive i h2 model A tag ≤ GeneralPaperSegmentCallbackLifetime.pairProfile model A s := by
  subst m
  have hEnv : ∀ j, RationalHeight ((GeneralPaperPairSegmentPreparation.environment i.B A).1.read j) s := by
    intro j
    rw [GeneralPaperPairSegmentPreparation.environment_data, FixedArrayTable.read_ofFn]
    exact h.1
  cases tag with
  | weight slot => exact GeneralPaperSegmentCallbackLifetime.pair_weight model A _ s hs slot
  | left slot j => exact (GeneralPaperSegmentCallbackLifetime.pair_endpoints model A _ s hs hEnv slot j).1
  | right slot j => exact (GeneralPaperSegmentCallbackLifetime.pair_endpoints model A _ s hs hEnv slot j).2

theorem triple_bound {m : ℕ} (i : RationalUniformGroupSpec m) (h3 : m = 3)
    (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (tag : Tag m) :
    tripleLive i h3 model A tag ≤ GeneralPaperSegmentCallbackLifetime.threeProfile model A s := by
  subst m
  have hEnv : ∀ j, RationalHeight ((GeneralPaperThreeSegmentPreparation.environment i.threeInput A).1.read j) s := by
    intro j
    rw [GeneralPaperThreeSegmentPreparation.environment_data]
    exact h.three_environment hs j
  cases tag with
  | weight slot => exact GeneralPaperSegmentCallbackLifetime.three_weight model A _ s hs hEnv slot
  | left slot j => exact GeneralPaperSegmentCallbackLifetime.three_left model A _ s hs hEnv slot j
  | right slot j => exact GeneralPaperSegmentCallbackLifetime.three_right model A _ s hs hEnv slot j

theorem bounded {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (tag : Tag m) :
    live i size hSize hm model A tag ≤ profile model A s := by
  unfold live profile
  split
  · exact (pair_bound i _ model A s hs h tag).trans (Nat.le_add_right _ _)
  · exact (triple_bound i _ model A s hs h tag).trans (Nat.le_add_left _ _)

theorem headline (model : RationalCostModel) (A s : ℕ) :
    profile model A s ≤ 70368744177664 * (model.rat (1 + 2 * expressionHeightBudget s 20) + A + 1) := by
  have hHeight := expressionHeightBudget_ge_input s 20
  have hRat := model.monotone (show 1 + 2 * s ≤ 1 + 2 * expressionHeightBudget s 20 by omega)
  have hPositive := model.word_le (1 + 2 * expressionHeightBudget s 20)
  have h2 : binaryWordWidth 2 = 2 := by decide
  have h6 : binaryWordWidth 6 = 3 := by decide
  unfold profile GeneralPaperSegmentCallbackLifetime.pairProfile GeneralPaperSegmentCallbackLifetime.threeProfile
    GeneralPaperExpressionBitExecution.nodeBound GeneralPaperExpressionBitExecution.unit
  rw [h2, h6]
  omega

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small))
    (tag : Tag (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).groups.length) :
    live (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)) p.groups.data.size p.groups.size
      (GeneralPaperEqualFiniteKernel.terminal _ small).groups_count model A tag ≤
      70368744177664 * (model.rat (4194304 * (binaryWordWidth n + exponent + 10)) + A + 1) := by
  have hs : 2 ≤ GeneralPaperEqualNativeSampler.fieldHeight n exponent := by
    unfold GeneralPaperEqualNativeSampler.fieldHeight
    omega
  have h := bounded (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)) p.groups.data.size p.groups.size
    (GeneralPaperEqualFiniteKernel.terminal _ small).groups_count model A _ hs
    (GeneralPaperEqualNativeSegmentPreparation.fields_height bits model W exponent values v hv small p) tag
  have hArg : 1 + 2 * expressionHeightBudget (GeneralPaperEqualNativeSampler.fieldHeight n exponent) 20 ≤
      4194304 * (binaryWordWidth n + exponent + 10) := by
    unfold GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
    omega
  have hRat := model.monotone hArg
  exact (h.trans (headline model A _)).trans (Nat.mul_le_mul_left 70368744177664 (by omega))

end Blotto.GeneralPaperNativeSegmentCallbackStorage
