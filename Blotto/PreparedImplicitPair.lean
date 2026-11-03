import Blotto.PreparedImplicitBatch

/-! Independent whole-player draws use separate fixed fair-bit blocks from
stored implicit samplers. Arbitrary joint bounded-test error adds; coordinates
within each row remain dependent. Equilibrium and original-game transfer are
separate obligations. -/

namespace Blotto.ImplicitLeafCounts.PreparedImplicitSampler

def pair (first second : PreparedImplicitSampler) (epsilonFirst epsilonSecond : ℚ)
    (bits : Fin (first.bitBudget epsilonFirst + second.bitBudget epsilonSecond) → Bool) : first.Row × second.Row :=
  (first.drawRow epsilonFirst (firstBitBlock _ _ bits), second.drawRow epsilonSecond (secondBitBlock _ _ bits))

theorem pair_feasible (first second : PreparedImplicitSampler) (epsilonFirst epsilonSecond : ℚ)
    (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (bits : Fin (first.bitBudget epsilonFirst + second.bitBudget epsilonSecond) → Bool) :
    Feasible (first.budget : ℝ) (fun field => ((pair first second epsilonFirst epsilonSecond bits).1 field : ℝ)) ∧
      Feasible (second.budget : ℝ) (fun field => ((pair first second epsilonFirst epsilonSecond bits).2 field : ℝ)) :=
  ⟨(first.drawRow_contract epsilonFirst hFirst).1 _, (second.drawRow_contract epsilonSecond hSecond).1 _⟩

theorem pair_mean (first second : PreparedImplicitSampler) (epsilonFirst epsilonSecond : ℚ)
    (test : first.Row × second.Row → ℝ) :
    (fairBitKernel (first.bitBudget epsilonFirst + second.bitBudget epsilonSecond)).mean
      (fun bits => test (pair first second epsilonFirst epsilonSecond bits)) =
      (first.rowKernel true epsilonFirst).mean (fun firstRow =>
        (second.rowKernel true epsilonSecond).mean (fun secondRow => test (firstRow, secondRow))) :=
  fairBitKernel_blocks _ _ (fun firstBits secondBits =>
    test (first.drawRow epsilonFirst firstBits, second.drawRow epsilonSecond secondBits))

theorem pair_mean_error (first second : PreparedImplicitSampler) (epsilonFirst epsilonSecond : ℚ)
    (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond)
    (test : first.Row × second.Row → ℝ) (hTest : ∀ rows, 0 ≤ test rows ∧ test rows ≤ 1) :
    |(fairBitKernel (first.bitBudget epsilonFirst + second.bitBudget epsilonSecond)).mean
      (fun bits => test (pair first second epsilonFirst epsilonSecond bits)) -
      (first.rowKernel false epsilonFirst).mean (fun firstRow =>
        (second.rowKernel false epsilonSecond).mean (fun secondRow => test (firstRow, secondRow)))| ≤
          (epsilonFirst : ℝ) + (epsilonSecond : ℝ) := by
  have hKernel := BoundedExpectationKernel.bind_close (first.rowKernel true epsilonFirst) (first.rowKernel false epsilonFirst)
    (fun firstRow => (second.rowKernel true epsilonSecond).map (fun secondRow => (firstRow, secondRow)))
    (fun firstRow => (second.rowKernel false epsilonSecond).map (fun secondRow => (firstRow, secondRow)))
    (epsilonFirst : ℝ) (epsilonSecond : ℝ) (first.rowKernel_close epsilonFirst hFirst)
    (fun firstRow => BoundedExpectationKernel.map_close _ _ (fun secondRow => (firstRow, secondRow)) _
      (second.rowKernel_close epsilonSecond hSecond))
  rw [pair_mean]
  exact hKernel test hTest

end Blotto.ImplicitLeafCounts.PreparedImplicitSampler
