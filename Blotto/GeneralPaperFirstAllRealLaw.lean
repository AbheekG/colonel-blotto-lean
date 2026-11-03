import Blotto.GeneralPaperFirstAllRealDispatch

/-! Canonical original-game laws and every-output budgets of the tagged
real-model return. Both players use independent whole-player seeds. -/
namespace Blotto.GeneralPaperFirstAllRealLaw
open GeneralPaperOriginalRealInput GeneralPaperFirstAllRealDispatch
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def law (model : RationalCostModel) (p : Input) : Prepared model p → Bool → Mixed p.n
  | .oneField h rich poor, reciprocal => GeneralPaperAllBranchBitLaw.oneLaw h (if reciprocal then poor else rich)
  | .equal _ source, _ => GeneralPaperEqualRealBranch.outputLaw source
  | .unequal output, reciprocal => output.sampler.elim (PureBoundaryEquilibria.pointLaw (fun _ => 0)) (fun sampler =>
      GeneralPaperStoredStrategySampler.law false (fun _ => 1) 1 model sampler reciprocal)

def Guarantee (model : RationalCostModel) (p : Input) (output : Prepared model p) : Prop :=
  let rich := law model p output false
  let poor := law model p output true
  Supported 1 rich ∧ Supported (p.budget : ℝ) poor ∧
    regret p.selector.values 1 rich poor ≤ (p.epsilon : ℝ) ∧
    regret p.selector.values (p.budget : ℝ) poor rich ≤ (p.epsilon : ℝ)

def Pointwise (model : RationalCostModel) (p : Input) : Prepared model p → Prop
  | .oneField h rich poor =>
      FullBudget 1 (GeneralPaperAllBranchBitOutput.oneAllocation h rich) ∧
      FullBudget (p.budget : ℝ) (GeneralPaperAllBranchBitOutput.oneAllocation h poor)
  | .equal k source => ∀ (u : ℝ) (fresh : Fin (k + 5) → Bool),
      FullBudget 1 (GeneralPaperEqualRealBranchDraw.run source u fresh).output.read ∧
      FullBudget (p.budget : ℝ) (GeneralPaperEqualRealBranchDraw.run source u fresh).output.read
  | .unequal output => output.sampler.elim False (fun sampler =>
      ∀ fresh : Fin (sampler.controls.rowBits + sampler.controls.shiftBits) → Bool,
        Feasible 1 (fun j => ((GeneralPaperStoredStrategySampler.run false (fun _ => 1) 1 model sampler false fresh).output.read j : ℝ)) ∧
        Feasible (p.budget : ℝ) (fun j => ((GeneralPaperStoredStrategySampler.run false (fun _ => 1) 1 model sampler true fresh).output.read j : ℝ)))

end Blotto.GeneralPaperFirstAllRealLaw
