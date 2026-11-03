import Blotto.GeneralPaperFirstMeasuredEqualContract

/-! Computable original-input bit dispatch. The program selects the boundary
case before preparation; each remaining branch prepares accuracy and the
reference once, retaining both for all subsequent construction. -/
namespace Blotto.GeneralPaperFirstAllBitDispatch
open GeneralPaperOriginalGameInput
open GeneralPaperAllBranchBitDispatch (Prepared one branchPrice)
open GeneralPaperFirstAllBitLaw (Guarantee Pointwise)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def run (model : RationalCostModel) (K : ℕ) (p : Input) : Option (Prepared p.n) × ℕ :=
  if hN : p.n = 1 then
    let actual := one p hN
    (some actual.1, actual.2 + 64 * (binaryWordWidth p.n + 1))
  else if hB : p.budget = 1 then
    let actual := GeneralPaperFirstMeasuredEqualPreparation.run model 1 K p
    (actual.1, actual.2 + branchPrice model p)
  else
    let actual := GeneralPaperMeasuredUnequalPreparation.run model 1 K p (strict_of_ne p hB)
    (some (.unequal actual.1), actual.2 + branchPrice model p)

theorem on_one (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n = 1) :
    run model K p = (some (one p hN).1, (one p hN).2 + 64 * (binaryWordWidth p.n + 1)) := by
  simp [run, hN]

theorem on_equal (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget = 1) :
    run model K p = ((GeneralPaperFirstMeasuredEqualPreparation.run model 1 K p).1,
      (GeneralPaperFirstMeasuredEqualPreparation.run model 1 K p).2 + branchPrice model p) := by
  simp [run, hN, hB]

theorem on_unequal (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n ≠ 1) (hB : p.budget ≠ 1) :
    run model K p =
      (some (.unequal (GeneralPaperMeasuredUnequalPreparation.run model 1 K p (strict_of_ne p hB)).1),
        (GeneralPaperMeasuredUnequalPreparation.run model 1 K p (strict_of_ne p hB)).2 + branchPrice model p) := by
  simp [run, hN, hB]

theorem always_returns (model : RationalCostModel) (K : ℕ) (p : Input) :
    ∃ output, (run model K p).1 = some output := by
  by_cases hN : p.n = 1
  · exact ⟨_, by rw [on_one model K p hN]⟩
  · by_cases hB : p.budget = 1
    · obtain ⟨output, hReturn, _⟩ := GeneralPaperFirstMeasuredEqualPreparation.returns model 1 K p
      exact ⟨.equal _ output, by rw [on_equal model K p hN hB]; exact hReturn⟩
    · exact ⟨_, by rw [on_unequal model K p hN hB]⟩

set_option maxHeartbeats 100000 in
theorem original_game_contract (model : RationalCostModel) (K : ℕ) (p : Input) (hOne : epsilon p < 1) :
    ∃ output, (run model K p).1 = some output ∧ Guarantee model K p output ∧ Pointwise model K p output := by
  by_cases hN : p.n = 1
  · refine ⟨(one p hN).1, ?_, GeneralPaperAllBranchBitCorrectness.one_correct model K p hN,
      GeneralPaperAllBranchBitOutput.one_outputs model K p hN⟩
    rw [on_one model K p hN]
  · by_cases hB : p.budget = 1
    · obtain ⟨output, hReturn, hLaw, hPointwise⟩ := GeneralPaperFirstMeasuredEqualContract.constructed model 1 K p hB hOne
      refine ⟨output, ?_, hLaw, hPointwise⟩
      rw [on_equal model K p hN hB]
      exact hReturn
    · obtain ⟨hLaw, hPointwise⟩ := GeneralPaperMeasuredUnequalContract.actual_contract model 1 K p
        (strict_of_ne p hB) hOne
      let actual := (GeneralPaperMeasuredUnequalPreparation.run model 1 K p (strict_of_ne p hB)).1
      refine ⟨.unequal actual, ?_, ?_, ?_⟩
      · rw [on_unequal model K p hN hB]
      · change GeneralPaperAllBranchBitLaw.Guarantee model K p (.unequal actual)
        exact hLaw
      · change GeneralPaperAllBranchBitOutput.Pointwise model K p (.unequal actual)
        exact hPointwise

theorem every_returned (model : RationalCostModel) (K : ℕ) (p : Input) (hOne : epsilon p < 1)
    (output : Prepared p.n) (hReturn : (run model K p).1 = some output) :
    Guarantee model K p output ∧ Pointwise model K p output := by
  obtain ⟨actual, hActual, hLaw, hPointwise⟩ := original_game_contract model K p hOne
  have hEq := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact ⟨hLaw, hPointwise⟩


theorem one_eq_preserved (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n=1) :
    run model K p=GeneralPaperMeasuredBitDispatch.run model K p := by
  rw [on_one model K p hN,GeneralPaperMeasuredBitDispatch.on_one model K p hN]

theorem unequal_eq_preserved (model : RationalCostModel) (K : ℕ) (p : Input) (hN : p.n≠1) (hB : p.budget≠1) :
    run model K p=GeneralPaperMeasuredBitDispatch.run model K p := by
  rw [on_unequal model K p hN hB,GeneralPaperMeasuredBitDispatch.on_unequal model K p hN hB]

end Blotto.GeneralPaperFirstAllBitDispatch
