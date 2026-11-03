import Blotto.GeneralPaperEqualBitContinuation

/-! The actual bit selector returns a pure stored row or the full Boolean
bit sampler. Its erased real view connects both branches to the checked
canonical continuous-game law, without executing real-model preparation. -/
namespace Blotto.GeneralPaperEqualBitBranch
open MeasureTheory
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 2000000

inductive Prepared {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (budget : ℚ) where
  | dominant (chosen : Fin n) (heavy : (1 / 2 : ℚ) ≤ v.weight chosen)
      (row : RationalResourceArray n)
      (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
  | grouped (small : ∀ j, 2 * v.weight j ≤ 1)
      (sampler : GeneralPaperEqualStoredBitSampler.Sampler (terminal v small).partition (lottery v small))
      (precision : sampler.exponent = k) (originalBudget : sampler.prepared.budget = budget)

noncomputable def outputLaw {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    Prepared v k budget → Mixed n
  | .dominant _ _ row _ => PureBoundaryEquilibria.pointLaw row.realAllocation
  | .grouped _ sampler _ _ => GeneralPaperEqualStoredBitSampler.outputLaw sampler model

def realView {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    Prepared v k budget → GeneralPaperEqualRealBranch.Prepared v k budget
  | .dominant chosen heavy row correct => .dominant chosen heavy row correct
  | .grouped small sampler hK hB => .grouped small (GeneralPaperEqualRealCache.project sampler.prepared)
      (sampler.exponent_correct.trans (congrArg (fun k => k + 5) hK)) hB

theorem law_realView {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) : outputLaw model p = GeneralPaperEqualRealBranch.outputLaw (realView p) := by
  cases p with
  | dominant chosen heavy row correct => rfl
  | grouped small sampler hK hB =>
    simp only [outputLaw, realView, GeneralPaperEqualRealBranch.outputLaw,
      GeneralPaperEqualRealCacheDraw.outputLaw_eq, GeneralPaperEqualRealCache.view_project]
    exact GeneralPaperEqualFullBitOutput.real_bit_law sampler model

theorem rounded_regret {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (hB : 0 < budget) :
    Supported (budget : ℝ) (outputLaw model p) ∧
      regret v.values (budget : ℝ) (outputLaw model p) (outputLaw model p) ≤ (1 / (2 : ℝ) ^ k) / 32 := by
  rw [law_realView]
  exact GeneralPaperEqualRealBranch.rounded_regret (realView p) hB

def prepare {n : ℕ} (model : RationalCostModel) (A k : ℕ) (v : RationalFieldSelector n) (budget : ℚ)
    (lengths : FixedArrayTable n ℚ) (hL : ∀ j, lengths.read j = 2 * v.weight j) : Prepared v k budget × ℕ :=
  let scanned := GeneralPaperEqualBitBoundaryScan.run model A lengths
  match h : scanned.1 with
  | some chosen =>
    let heavy := GeneralPaperEqualRealBoundaryScan.some_heavy lengths v hL chosen
      ((GeneralPaperEqualBitBoundaryScan.run_data model A lengths).symm.trans h)
    let row := GeneralPaperEqualBitVertex.run A budget chosen
    (.dominant chosen heavy row.1 (GeneralPaperEqualBitVertex.data A budget chosen), scanned.2 + row.2 + 64 * A + 64)
  | none =>
    let small := GeneralPaperEqualRealBoundaryScan.none_small lengths v hL
      ((GeneralPaperEqualBitBoundaryScan.run_data model A lengths).symm.trans h)
    let made := GeneralPaperEqualBitContinuation.run model A k v small lengths hL budget
    (.grouped small made.1 rfl rfl, scanned.2 + made.2 + 64 * A + 64)

end Blotto.GeneralPaperEqualBitBranch
