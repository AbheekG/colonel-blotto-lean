import Blotto.GeneralPaperAllBranchBitLaw

/-! Canonical continuous-game correctness of all original-input branches.
No finite-response, source-success or branch certificate is supplied by
the caller. Costs and executable calibration erasure remain separate joins. -/
namespace Blotto.GeneralPaperAllBranchBitCorrectness
open GeneralPaperOriginalGameInput GeneralPaperAllBranchBitDispatch GeneralPaperAllBranchBitLaw
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 16384

theorem one_correct (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    Guarantee model K p (one p hN).1 := by
  rcases p with ⟨n,values,selector,correct,words,b,hBudget⟩
  change n = 1 at hN
  subst n
  let p : Input := ⟨1,values,selector,correct,words,b,hBudget⟩
  have h := GeneralPaperOneFieldRealPreparation.equilibrium selector.values 1 b (by norm_num) hBudget.1.le
  have hE : (0 : ℝ) ≤ epsilon p := by exact_mod_cast (epsilon_positive p).le
  change Supported 1 (PureBoundaryEquilibria.pointLaw (GeneralPaperOneFieldRealPreparation.run 1 b).1.1.realAllocation) ∧
    Supported (b : ℝ) (PureBoundaryEquilibria.pointLaw (GeneralPaperOneFieldRealPreparation.run 1 b).1.2.realAllocation) ∧ _ ∧ _
  dsimp only at h
  simp only [Rat.cast_one] at h
  refine ⟨h.1,h.2.1,?_,?_⟩
  · exact h.2.2.1.le.trans hE
  · exact h.2.2.2.le.trans hE

theorem equal_correct (model : RationalCostModel) (K : ℕ) (p : Input) (hB : p.budget = 1) (hOne : epsilon p < 1)
    (output : GeneralPaperUnifiedDirectoryInstallation.Installed
      (GeneralPaperStoredSelectedPipeline.width model (GeneralPaperEqualInputDomain.word K (equalInput model p)) K (equalInput model p)))
    (hReturn : (GeneralPaperStoredSelectedPipeline.run model (GeneralPaperEqualInputDomain.word K (equalInput model p)) K
      (equalInput model p)).1 = some output) :
    Guarantee model K p (.equal _ output) := by
  have h := GeneralPaperStoredSelectedPipeline.epsilon model (GeneralPaperEqualInputDomain.word K (equalInput model p)) K
    (equalInput model p) hOne p.budget_valid.1 output hReturn
  change Supported (p.budget : ℝ) (law model K p (.equal _ output) false) ∧
    regret p.selector.values (p.budget : ℝ) (law model K p (.equal _ output) false)
      (law model K p (.equal _ output) false) ≤ (epsilon p : ℝ) at h
  change Supported 1 (law model K p (.equal _ output) false) ∧
    Supported (p.budget : ℝ) (law model K p (.equal _ output) false) ∧ _ ∧ _
  rw [hB,Rat.cast_one] at h ⊢
  exact ⟨h.1,h.1,h.2,h.2⟩

theorem unequal_correct (model : RationalCostModel) (C d K : ℕ) (p : Input) (hStrict : p.budget < 1)
    (hOne : epsilon p < 1) : Guarantee model K p (unequal model C d p hStrict).1 := by
  let W := GeneralPaperNativeResourceReferenceGrowth.word model C d (unequalInput p hStrict)
  let actual := (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1,hStrict⟩).1
  obtain ⟨sampler,hSampler,_⟩ := GeneralPaperClosedStrategyEquilibrium.bit_epsilon model W W W p.words
    (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget ⟨p.budget_valid.1,hStrict⟩ model.rat
  have hG := GeneralPaperNativeSamplerViewAndLaw.native_epsilon_at_draw_reference true model.rat
    (GeneralPaperClosedBitSampling.reference p.n actual.raw.strategies.original.reduced.m actual.raw.exponent)
    model W W W p.words (epsilon p) (epsilon_positive p) hOne rfl p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1,hStrict⟩ sampler hSampler
  change Guarantee model K p (.unequal actual)
  dsimp only [Guarantee,law]
  change actual.sampler = some sampler at hSampler
  simp only [hSampler,Option.elim_some]
  exact ⟨hG.1,hG.2.1,hG.2.2.1,hG.2.2.2.1⟩

theorem constructed (model : RationalCostModel) (C d K : ℕ) (p : Input) (hOne : epsilon p < 1) :
    ∃ output,(run model C d K p).1 = some output ∧ Guarantee model K p output := by
  by_cases hN : p.n = 1
  · refine ⟨(one p hN).1,?_,one_correct model K p hN⟩
    rw [on_one model C d K p hN]
  · by_cases hB : p.budget = 1
    · let input := equalInput model p
      let W := GeneralPaperEqualInputDomain.word K input
      obtain ⟨output,hReturn,_,_⟩ := GeneralPaperStoredSelectedPipeline.source model W K input
      refine ⟨.equal (GeneralPaperStoredSelectedPipeline.width model W K input) output,?_,
        equal_correct model K p hB hOne output hReturn⟩
      rw [on_equal model C d K p hN hB]
      simp only [equal]
      change ((GeneralPaperStoredSelectedPipeline.run model W K input).1.map _) = _
      rw [hReturn]
      rfl
    · refine ⟨(unequal model C d p (strict_of_ne p hB)).1,?_,
        unequal_correct model C d K p (strict_of_ne p hB) hOne⟩
      rw [on_unequal model C d K p hN hB]

theorem every_returned (model : RationalCostModel) (C d K : ℕ) (p : Input) (hOne : epsilon p < 1)
    (output : Prepared p.n) (hReturn : (run model C d K p).1 = some output) : Guarantee model K p output := by
  obtain ⟨actual,hActual,hCorrect⟩ := constructed model C d K p hOne
  have hEq := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hCorrect

end Blotto.GeneralPaperAllBranchBitCorrectness
