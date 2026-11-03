import Blotto.GeneralPaperFirstAllRealLaw

/-! Continuous-game correctness and pointwise original budgets of every
actual real-model branch, with the branch chosen by the program. -/
namespace Blotto.GeneralPaperFirstAllRealCorrectness
open GeneralPaperOriginalRealInput GeneralPaperFirstAllRealDispatch GeneralPaperFirstAllRealLaw
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem one_correct (model : RationalCostModel) (p : Input) (hN : p.n = 1) :
    Guarantee model p (one model p hN).1 ∧ Pointwise model p (one model p hN).1 := by
  rcases p with ⟨n, values, selector, correct, eps, hEps, b, hBudget⟩
  change n = 1 at hN
  subst n
  have he : (0 : ℝ) ≤ eps := by exact_mod_cast hEps.1.le
  have h := GeneralPaperOneFieldRealPreparation.equilibrium selector.values 1 b (by norm_num) hBudget.1.le
  have hb := GeneralPaperOneFieldRealPreparation.every_output 1 b (by norm_num) hBudget.1.le
  constructor
  · change Supported 1 (PureBoundaryEquilibria.pointLaw (GeneralPaperOneFieldRealPreparation.run 1 b).1.1.realAllocation) ∧
      Supported (b : ℝ) (PureBoundaryEquilibria.pointLaw (GeneralPaperOneFieldRealPreparation.run 1 b).1.2.realAllocation) ∧ _ ∧ _
    dsimp only at h
    simp only [Rat.cast_one] at h
    exact ⟨h.1, h.2.1, h.2.2.1.le.trans he, h.2.2.2.le.trans he⟩
  · simpa only [Pointwise, one, GeneralPaperAllBranchBitOutput.oneAllocation, Rat.cast_one] using hb

theorem equal_correct (model : RationalCostModel) (p : Input) (hB : p.budget = 1) :
    Guarantee model p (equal model p).1 ∧ Pointwise model p (equal model p).1 := by
  have h := GeneralPaperEqualFirstRealDispatch.epsilon model p.epsilon p.epsilon_valid.1 p.epsilon_valid.2
    p.values p.selector p.correct p.budget p.budget_valid.1
  constructor
  · change Supported (p.budget : ℝ) (law model p (equal model p).1 false) ∧
      regret p.selector.values (p.budget : ℝ) (law model p (equal model p).1 false)
        (law model p (equal model p).1 false) ≤ (p.epsilon : ℝ) at h
    change Supported 1 (law model p (equal model p).1 false) ∧
      Supported (p.budget : ℝ) (law model p (equal model p).1 false) ∧ _ ∧ _
    rw [hB, Rat.cast_one] at h ⊢
    exact ⟨h.1, h.1, h.2, h.2⟩
  · intro u fresh
    have hb := GeneralPaperEqualRealBranchDraw.hard_budget
      (GeneralPaperEqualFirstRealDispatch.run model (GeneralPaperDyadicAccuracy.prepare p.epsilon).exponent
        p.values p.selector p.correct p.budget).1 p.budget_valid.1.le u fresh
    change FullBudget 1 _ ∧ FullBudget (p.budget : ℝ) _
    rw [hB, Rat.cast_one] at hb ⊢
    exact ⟨hb, hb⟩

theorem unequal_correct (model : RationalCostModel) (p : Input) (hB : p.budget < 1) :
    Guarantee model p (unequal model p).1 ∧ Pointwise model p (unequal model p).1 := by
  obtain ⟨sampler, hSampler, hG⟩ := GeneralPaperClosedStrategyEquilibrium.arithmetic_epsilon model
    p.epsilon p.epsilon_valid.1 p.epsilon_valid.2 p.values p.selector p.correct p.budget ⟨p.budget_valid.1, hB⟩ (fun _ => 1)
  constructor
  · dsimp only [Guarantee, law, unequal]
    simp only [hSampler, Option.elim_some]
    exact ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1⟩
  · dsimp only [Pointwise, unequal]
    simp only [hSampler, Option.elim_some]
    exact hG.2.2.2.2

theorem actual_contract (model : RationalCostModel) (p : Input) :
    Guarantee model p (run model p).1 ∧ Pointwise model p (run model p).1 := by
  by_cases hN : p.n = 1
  · rw [on_one model p hN]
    exact one_correct model p hN
  · by_cases hB : p.budget = 1
    · rw [on_equal model p hN hB]
      exact equal_correct model p hB
    · rw [on_unequal model p hN hB]
      exact unequal_correct model p (strict_of_ne p hB)

end Blotto.GeneralPaperFirstAllRealCorrectness
