import Blotto.GeneralPaperEqualFirstDescription

/-! The corrected numeric-real all-branch entry joins preparation time,
canonical continuous-game laws, every-output budgets, exact sampling and
the paper's uniform whole-row list for unequal budgets. -/
namespace Blotto.GeneralPaperFirstRealAlgorithmContract
open GeneralPaperOriginalRealInput GeneralPaperFirstAllRealDispatch
set_option autoImplicit false

def UniformList (model : RationalCostModel) (p : Input) : Prepared model p → Prop
  | .oneField _ _ _ => True
  | .equal _ _ => True
  | .unequal output => GeneralPaperUniformListReturns.Contract p.epsilon output

theorem uniform_list (model : RationalCostModel) (p : Input) : UniformList model p (run model p).1 := by
  by_cases hN : p.n = 1
  · rw [on_one model p hN]
    trivial
  · by_cases hB : p.budget = 1
    · rw [on_equal model p hN hB]
      trivial
    · rw [on_unequal model p hN hB]
      exact GeneralPaperUniformListReturns.numeric model p (strict_of_ne p hB)

theorem actual_contract (model : RationalCostModel) :
    ∃ C d : ℕ, ∀ p : Input, ((run model p).2 : ℚ) ≤
      (C : ℚ)*GeneralPaperRealHeadlineParameters.timeScale p.n p.epsilon*
        (GeneralPaperRealHeadlineParameters.logarithm p.n p.epsilon : ℚ)^d ∧
      GeneralPaperFirstAllExactRealLaw.Guarantee model p (run model p).1 ∧
      GeneralPaperFirstAllExactRealLaw.Pointwise model p (run model p).1 ∧
      GeneralPaperFirstAllExactRealSampling.Contract model p (run model p).1 ∧
      UniformList model p (run model p).1 := by
  obtain ⟨C,d,h⟩ := GeneralPaperFirstAllExactRealSampling.time_game_and_sampling model
  exact ⟨C,d,fun p => ⟨(h p).1,(h p).2.1,(h p).2.2.1,(h p).2.2.2,uniform_list model p⟩⟩

end Blotto.GeneralPaperFirstRealAlgorithmContract
