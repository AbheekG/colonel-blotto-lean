import Blotto.GeneralPaperExactRealSampler
import Blotto.GeneralPaperFirstAllRealTime

/-! Canonical original-game laws and every-output budgets of the tagged
real-model return. Both players use independent whole-player seeds. -/
namespace Blotto.GeneralPaperFirstAllExactRealLaw
open GeneralPaperOriginalRealInput GeneralPaperFirstAllRealDispatch
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def law (model : RationalCostModel) (p : Input) : Prepared model p → Bool → Mixed p.n
  | .oneField h rich poor, reciprocal => GeneralPaperAllBranchBitLaw.oneLaw h (if reciprocal then poor else rich)
  | .equal _ source, _ => GeneralPaperEqualRealBranch.outputLaw source
  | .unequal output, reciprocal => output.sampler.elim (PureBoundaryEquilibria.pointLaw (fun _ => 0)) (fun sampler =>
      GeneralPaperExactStoredSampler.law false (fun _ => 1) 1 model sampler reciprocal)

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
      ∀ fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool,
        Feasible 1 (fun j => ((GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler false fresh).output.read j : ℝ)) ∧
        Feasible (p.budget : ℝ) (fun j => ((GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler true fresh).output.read j : ℝ)))

theorem reference_law (model : RationalCostModel) (p : Input) (output : Prepared model p) (poor : Bool) :
    law model p output poor = GeneralPaperFirstAllRealLaw.law model p output poor := by
  cases output with
  | oneField h rich poorRow => rfl
  | equal k source => rfl
  | unequal output =>
    cases h : output.sampler with
    | none => simp only [law, GeneralPaperFirstAllRealLaw.law, h, Option.elim_none]
    | some sampler =>
      simp only [law, GeneralPaperFirstAllRealLaw.law, h, Option.elim_some]
      exact GeneralPaperExactStoredSampler.old_law false (fun _ => 1) 1 model sampler poor

theorem guarantee_of_reference (model : RationalCostModel) (p : Input) (output : Prepared model p)
    (h : GeneralPaperFirstAllRealLaw.Guarantee model p output) : Guarantee model p output := by
  simpa only [Guarantee, GeneralPaperFirstAllRealLaw.Guarantee, reference_law] using h

theorem pointwise_of_reference (model : RationalCostModel) (p : Input) (output : Prepared model p)
    (hG : GeneralPaperFirstAllRealLaw.Guarantee model p output)
    (hP : GeneralPaperFirstAllRealLaw.Pointwise model p output) : Pointwise model p output := by
  cases output with
  | oneField h rich poor => exact hP
  | equal k source => exact hP
  | unequal output =>
    cases hs : output.sampler with
    | none => simp only [GeneralPaperFirstAllRealLaw.Pointwise, hs, Option.elim_none] at hP
    | some sampler =>
      simp only [Pointwise, hs, Option.elim_some]
      simp only [GeneralPaperFirstAllRealLaw.Guarantee, GeneralPaperFirstAllRealLaw.law, hs, Option.elim_some] at hG
      intro fresh
      exact ⟨GeneralPaperExactStoredSampler.every_output_feasible false (fun _ => 1) 1 model sampler false 1 hG.1 fresh,
        GeneralPaperExactStoredSampler.every_output_feasible false (fun _ => 1) 1 model sampler true (p.budget : ℝ) hG.2.1 fresh⟩

end Blotto.GeneralPaperFirstAllExactRealLaw
