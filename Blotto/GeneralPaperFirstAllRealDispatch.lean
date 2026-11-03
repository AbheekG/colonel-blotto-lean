import Blotto.GeneralPaperEqualFirstBitWork

/-! One real-model entry, with the one-field test first. The equal branch
selects its dyadic exponent once and passes it directly to preparation. -/
namespace Blotto.GeneralPaperFirstAllRealDispatch
open GeneralPaperOriginalRealInput
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

inductive Prepared (model : RationalCostModel) (p : Input)
  | oneField (h : p.n = 1) (rich poor : RationalResourceArray 1)
  | equal (k : ℕ) (source : GeneralPaperEqualRealBranch.Prepared
      (GeneralPaperEqualFirstRounding.rounded false model 1 k p.values p.selector p.correct) k p.budget)
  | unequal (source : GeneralPaperClosedStrategyDriver.Prepared p.n)

def one (model : RationalCostModel) (p : Input) (h : p.n = 1) : Prepared model p × ℕ :=
  let actual := GeneralPaperOneFieldRealPreparation.run 1 p.budget
  (.oneField h actual.1.1 actual.1.2, actual.2)

def equal (model : RationalCostModel) (p : Input) : Prepared model p × ℕ :=
  let accuracy := GeneralPaperDyadicAccuracy.prepare p.epsilon
  let actual := GeneralPaperEqualFirstRealDispatch.run model accuracy.exponent p.values p.selector p.correct p.budget
  (.equal accuracy.exponent actual.1, accuracy.work + actual.2 + 64)

noncomputable def unequal (model : RationalCostModel) (p : Input) : Prepared model p × ℕ :=
  let actual := GeneralPaperClosedStrategyDriver.arithmetic model p.epsilon p.values p.selector p.correct p.budget
  (.unequal actual.1, actual.2)

noncomputable def run (model : RationalCostModel) (p : Input) : Prepared model p × ℕ :=
  if hN : p.n = 1 then
    let actual := one model p hN
    (actual.1, actual.2 + 64)
  else if p.budget = 1 then
    let actual := equal model p
    (actual.1, actual.2 + 96)
  else
    let actual := unequal model p
    (actual.1, actual.2 + 96)

theorem on_one (model : RationalCostModel) (p : Input) (hN : p.n = 1) :
    run model p = ((one model p hN).1, (one model p hN).2 + 64) := by simp [run, hN]

theorem on_equal (model : RationalCostModel) (p : Input) (hN : p.n ≠ 1) (hB : p.budget = 1) :
    run model p = ((equal model p).1, (equal model p).2 + 96) := by simp [run, hN, hB]

theorem on_unequal (model : RationalCostModel) (p : Input) (hN : p.n ≠ 1) (hB : p.budget ≠ 1) :
    run model p = ((unequal model p).1, (unequal model p).2 + 96) := by simp [run, hN, hB]

end Blotto.GeneralPaperFirstAllRealDispatch
