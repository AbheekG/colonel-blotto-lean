import Blotto.GeneralPaperFirstAlgorithmContract

/-! The last sentence of thm:general: for one battlefield the returned
strategies form an exact equilibrium. `actual_contract` states only the
epsilon bound; both the bit and the real dispatch return the two full-budget
vertices, whose regrets are zero. -/
namespace Blotto.GeneralPaperOneFieldExact
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem bit_exact (model : RationalCostModel) (K : ℕ) (p : GeneralPaperOriginalGameInput.Input)
    (hN : p.n = 1) :
    ∃ output, (GeneralPaperFirstAllBitDispatch.run model K p).1 = some output ∧
      regret p.selector.values 1 (GeneralPaperFirstAllBitLaw.law model K p output false)
        (GeneralPaperFirstAllBitLaw.law model K p output true) = 0 ∧
      regret p.selector.values (p.budget : ℝ) (GeneralPaperFirstAllBitLaw.law model K p output true)
        (GeneralPaperFirstAllBitLaw.law model K p output false) = 0 := by
  refine ⟨(GeneralPaperAllBranchBitDispatch.one p hN).1,
    by rw [GeneralPaperFirstAllBitDispatch.on_one model K p hN],?_⟩
  rcases p with ⟨n,values,selector,correct,words,b,hBudget⟩
  change n = 1 at hN
  subst n
  have h := GeneralPaperOneFieldRealPreparation.equilibrium selector.values 1 b (by norm_num) hBudget.1.le
  dsimp only at h
  simp only [Rat.cast_one] at h
  exact ⟨h.2.2.1,h.2.2.2⟩

theorem real_exact (model : RationalCostModel) (p : GeneralPaperOriginalRealInput.Input) (hN : p.n = 1) :
    let output := (GeneralPaperFirstAllRealDispatch.run model p).1
    regret p.selector.values 1 (GeneralPaperFirstAllExactRealLaw.law model p output false)
        (GeneralPaperFirstAllExactRealLaw.law model p output true) = 0 ∧
      regret p.selector.values (p.budget : ℝ) (GeneralPaperFirstAllExactRealLaw.law model p output true)
        (GeneralPaperFirstAllExactRealLaw.law model p output false) = 0 := by
  dsimp only
  rw [GeneralPaperFirstAllRealDispatch.on_one model p hN]
  rcases p with ⟨n,values,selector,correct,eps,hEps,b,hBudget⟩
  change n = 1 at hN
  subst n
  have h := GeneralPaperOneFieldRealPreparation.equilibrium selector.values 1 b (by norm_num) hBudget.1.le
  dsimp only at h
  simp only [Rat.cast_one] at h
  exact ⟨h.2.2.1,h.2.2.2⟩

end Blotto.GeneralPaperOneFieldExact
