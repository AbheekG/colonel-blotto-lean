import Blotto.GeneralPaperAllBranchBitCorrectness

/-! Pointwise original-budget contracts for the shared dispatcher. The
equal branch covers every completed common-runtime observation; the finite
unequal sampler covers every fresh-bit string, not merely almost surely. -/
namespace Blotto.GeneralPaperAllBranchBitOutput
open GeneralPaperOriginalGameInput GeneralPaperAllBranchBitDispatch GeneralPaperAllBranchBitLaw
open GeneralPaperEqualBitBranchDraw (Trace)
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 16384

noncomputable def oneAllocation {n : ℕ} (h : n = 1) (row : RationalResourceArray 1) : Allocation n := h.symm ▸ row.realAllocation

def Pointwise (model : RationalCostModel) (K : ℕ) (p : Input) : Prepared p.n → Prop
  | .oneField h rich poor => FullBudget 1 (oneAllocation h rich) ∧ FullBudget (p.budget : ℝ) (oneAllocation h poor)
  | .equal A output => ∀ (trace : Trace (equalSource model K p).branch) (row : Array ℚ),
      (GeneralPaperStoredSelectedLaw.observed model A output (equalSource model K p).branch trace).output = some row →
      row.size = p.n ∧ FullBudget 1 (fun j : Fin p.n => (row.getD j.val 0 : ℝ)) ∧
        FullBudget (p.budget : ℝ) (fun j : Fin p.n => (row.getD j.val 0 : ℝ))
  | .unequal output => output.sampler.elim False (fun sampler =>
      ∀ fresh : Fin (sampler.controls.rowBits + sampler.controls.shiftBits) → Bool,
        Feasible 1 (fun j => ((GeneralPaperStoredStrategySampler.run true model.rat
          (GeneralPaperClosedBitSampling.reference p.n output.raw.strategies.original.reduced.m output.raw.exponent)
          model sampler false fresh).output.read j : ℝ)) ∧
        Feasible (p.budget : ℝ) (fun j => ((GeneralPaperStoredStrategySampler.run true model.rat
          (GeneralPaperClosedBitSampling.reference p.n output.raw.strategies.original.reduced.m output.raw.exponent)
          model sampler true fresh).output.read j : ℝ)))

theorem one_outputs (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    Pointwise model K p (one p hN).1 := by
  rcases p with ⟨n,values,selector,correct,words,b,hBudget⟩
  change n = 1 at hN
  subst n
  have h := GeneralPaperOneFieldRealPreparation.every_output 1 b (by norm_num) hBudget.1.le
  simpa only [Pointwise,one,oneAllocation,Rat.cast_one] using h

theorem equal_outputs (model : RationalCostModel) (K : ℕ) (p : Input) (hB : p.budget = 1)
    (output : GeneralPaperUnifiedDirectoryInstallation.Installed
      (GeneralPaperStoredSelectedPipeline.width model (GeneralPaperEqualInputDomain.word K (equalInput model p)) K (equalInput model p)))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model (GeneralPaperEqualInputDomain.word K (equalInput model p)) K
      (equalInput model p)).1 = some output) : Pointwise model K p (.equal _ output) := by
  intro trace row hOutput
  have h := GeneralPaperStoredSelectedOutput.pipeline_written_output model
    (GeneralPaperEqualInputDomain.word K (equalInput model p)) K (equalInput model p) p.budget_valid.1.le output hReturn trace row hOutput
  change row.size = p.n ∧ FullBudget (p.budget : ℝ) _ ∧ _ at h
  rw [hB,Rat.cast_one] at h ⊢
  exact ⟨h.1,h.2.1,h.2.1⟩

theorem unequal_outputs (model : RationalCostModel) (C d K : ℕ) (p : Input) (hStrict : p.budget < 1)
    (hOne : epsilon p < 1) : Pointwise model K p (unequal model C d p hStrict).1 := by
  let W := GeneralPaperNativeResourceReferenceGrowth.word model C d (unequalInput p hStrict)
  let actual := (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1,hStrict⟩).1
  obtain ⟨sampler,hSampler,_⟩ := GeneralPaperClosedStrategyEquilibrium.bit_epsilon model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget ⟨p.budget_valid.1,hStrict⟩ model.rat
  have hG := GeneralPaperNativeSamplerViewAndLaw.native_epsilon_at_draw_reference true model.rat
    (GeneralPaperClosedBitSampling.reference p.n actual.raw.strategies.original.reduced.m actual.raw.exponent)
    model W W W p.words (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1,hStrict⟩ sampler hSampler
  change Pointwise model K p (.unequal actual)
  dsimp only [Pointwise]
  change actual.sampler = some sampler at hSampler
  simp only [hSampler,Option.elim_some]
  exact hG.2.2.2.2

theorem constructed (model : RationalCostModel) (C d K : ℕ) (p : Input) (hOne : epsilon p < 1) :
    ∃ output,(run model C d K p).1 = some output ∧ Pointwise model K p output := by
  by_cases hN : p.n = 1
  · refine ⟨(one p hN).1,?_,one_outputs model K p hN⟩
    rw [on_one model C d K p hN]
  · by_cases hB : p.budget = 1
    · let input := equalInput model p
      let W := GeneralPaperEqualInputDomain.word K input
      obtain ⟨output,hReturn,_,_⟩ := GeneralPaperStoredSelectedPipeline.source model W K input
      refine ⟨.equal (GeneralPaperStoredSelectedPipeline.width model W K input) output,?_,equal_outputs model K p hB output hReturn⟩
      rw [on_equal model C d K p hN hB]
      simp only [equal]
      change ((GeneralPaperStoredSelectedPipeline.run model W K input).1.map _) = _
      rw [hReturn]
      rfl
    · refine ⟨(unequal model C d p (strict_of_ne p hB)).1,?_,unequal_outputs model C d K p (strict_of_ne p hB) hOne⟩
      rw [on_unequal model C d K p hN hB]

theorem original_game_contract (model : RationalCostModel) (C d K : ℕ) (p : Input) (hOne : epsilon p < 1) :
    ∃ output,(run model C d K p).1 = some output ∧ Guarantee model K p output ∧ Pointwise model K p output := by
  obtain ⟨output,hReturn,hPointwise⟩ := constructed model C d K p hOne
  exact ⟨output,hReturn,GeneralPaperAllBranchBitCorrectness.every_returned model C d K p hOne output hReturn,hPointwise⟩

end Blotto.GeneralPaperAllBranchBitOutput
