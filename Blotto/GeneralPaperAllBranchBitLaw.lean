import Blotto.GeneralPaperAllBranchBitDispatch

/-! Canonical laws of the tagged original-input return. Source objects in
the equal law are proof observers; actual draws use the retained RAM/root.
The unequal law uses only the actual returned closed sampler. -/
namespace Blotto.GeneralPaperAllBranchBitLaw
open GeneralPaperOriginalGameInput GeneralPaperAllBranchBitDispatch
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

noncomputable def oneLaw {n : ℕ} (h : n = 1) (row : RationalResourceArray 1) : Mixed n :=
  h.symm ▸ PureBoundaryEquilibria.pointLaw row.realAllocation

def equalSource (model : RationalCostModel) (K : ℕ) (p : Input) :=
  (GeneralPaperEqualCopiedPipeline.run model (GeneralPaperEqualInputDomain.word K (equalInput model p)) K (equalInput model p)).1

noncomputable def law (model : RationalCostModel) (K : ℕ) (p : Input) : Prepared p.n → Bool → Mixed p.n
  | .oneField h rich poor,reciprocal => oneLaw h (if reciprocal then poor else rich)
  | .equal A output,_ => GeneralPaperStoredSelectedLaw.outputLaw model A output (equalSource model K p).branch
  | .unequal output,reciprocal =>
    output.sampler.elim (PureBoundaryEquilibria.pointLaw (fun _ => 0)) (fun sampler =>
      GeneralPaperStoredStrategySampler.law true model.rat
        (GeneralPaperClosedBitSampling.reference p.n output.raw.strategies.original.reduced.m output.raw.exponent)
        model sampler reciprocal)

def Guarantee (model : RationalCostModel) (K : ℕ) (p : Input) (output : Prepared p.n) : Prop :=
  let rich := law model K p output false
  let poor := law model K p output true
  Supported 1 rich ∧ Supported (p.budget : ℝ) poor ∧
    regret p.selector.values 1 rich poor ≤ (epsilon p : ℝ) ∧
    regret p.selector.values (p.budget : ℝ) poor rich ≤ (epsilon p : ℝ)

theorem equal_returns (model : RationalCostModel) (K : ℕ) (p : Input) :
    ∃ output,(equal model K p).1 = some output := by
  obtain ⟨output,hReturn,_,_⟩ := GeneralPaperStoredSelectedPipeline.source model
    (GeneralPaperEqualInputDomain.word K (equalInput model p)) K (equalInput model p)
  refine ⟨.equal _ output,?_⟩
  simp only [equal,hReturn,Option.map_some]

theorem always_returns (model : RationalCostModel) (C d K : ℕ) (p : Input) :
    ∃ output,(run model C d K p).1 = some output := by
  by_cases hN : p.n = 1
  · exact ⟨_,by rw [on_one model C d K p hN]⟩
  · by_cases hB : p.budget = 1
    · obtain ⟨output,hReturn⟩ := equal_returns model K p
      exact ⟨output,by rw [on_equal model C d K p hN hB]; exact hReturn⟩
    · exact ⟨_,by rw [on_unequal model C d K p hN hB]⟩

end Blotto.GeneralPaperAllBranchBitLaw
