import Blotto.GeneralPaperUniformSegmentPreparation

/-! The actual retained group array feeds the priced two/three factory.
Native short heights come from positive rounding and its denominator lattice;
no numeric mass/precision certificate is supplied to execution. -/
namespace Blotto.GeneralPaperEqualNativeSegmentPreparation
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualNativeSampler (rounded fieldHeight)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def source {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) :=
  (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small)).lottery (terminal v small).groups_count

def run {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) (model : RationalCostModel) (A : ℕ) :
    PreparedSegmentDescriptor (source v small p) × ℕ :=
  GeneralPaperUniformSegmentPreparation.run (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction v small))
    p.groups.data.size p.groups.size (terminal v small).groups_count model A

theorem source_eq {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) : source v small p = lottery v small := by
  unfold source GeneralPaperEqualFiniteKernel.lottery GeneralPaperEqualFiniteKernel.spec
  simp only [RationalTerminalPacking.uniformSpec_eq]

def prepared {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) (model : RationalCostModel) (A : ℕ) :
    PreparedSegmentDescriptor (lottery v small) × ℕ :=
  let actual := run v small p model A
  (cast (congrArg PreparedSegmentDescriptor (source_eq v small p)) actual.1, actual.2)

theorem prepared_data {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) (model : RationalCostModel) (A : ℕ) :
    (prepared v small p model A).1 = PreparedSegmentDescriptor.prepare (lottery v small) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

theorem data {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (p : RationalTerminalPacking (terminal v small)) (model : RationalCostModel) (A : ℕ) :
    (run v small p model A).1 = PreparedSegmentDescriptor.prepare (source v small p) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

theorem fields_height {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small)) :
    (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction (rounded bits model W k values v hv) small)).FieldsHeight (fieldHeight n k) := by
  have h := GeneralPaperEqualNativeSampler.native_spec_height bits model W k values v hv small
  unfold GeneralPaperEqualFiniteKernel.spec at h
  rw [RationalTerminalPacking.uniformSpec_eq] at h ⊢
  exact h

theorem native_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (terminal (rounded bits model W k values v hv) small)) :
    (run (rounded bits model W k values v hv) small p model A).2 ≤
      4294967296 * (model.rat (4194304 * (binaryWordWidth n + k + 10)) + A + 1) := by
  have hs : 2 ≤ fieldHeight n k := by unfold fieldHeight; omega
  have h := GeneralPaperUniformSegmentPreparation.work
    (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction (rounded bits model W k values v hv) small))
    p.groups.data.size p.groups.size (terminal (rounded bits model W k values v hv) small).groups_count
    model A (fieldHeight n k) hs (fields_height bits model W k values v hv small p)
  have hHead := GeneralPaperUniformSegmentPreparation.headline model A (fieldHeight n k)
  have hw : 1 + 2 * expressionHeightBudget (fieldHeight n k) 20 ≤
      4194304 * (binaryWordWidth n + k + 10) := by
    unfold fieldHeight expressionHeightBudget
    omega
  have hRat := model.monotone hw
  exact (h.trans hHead).trans (Nat.mul_le_mul_left 4294967296 (by omega))

end Blotto.GeneralPaperEqualNativeSegmentPreparation
