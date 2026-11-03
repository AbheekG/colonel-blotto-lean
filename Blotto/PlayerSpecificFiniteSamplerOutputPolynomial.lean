import Blotto.PlayerSpecificRationalFiniteOutputPolynomial
import Blotto.PlayerSpecificFiniteSamplerMeasuredSourceJoin

/-! The accepted public draw has the same native result and feasible
output, with its complete rational-output portion already bounded by an
explicit polynomial in the original input size and computed precisions. -/
namespace Blotto.PlayerSpecificFiniteSamplerOutputPolynomial
open PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem accepted_draws {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique
        p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval x ∧
      ∀ (player : Bool) (bits : Fin (bitCount p) → Bool),
        (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).1=
          PlayerSpecificFiniteSampler.draw p player bits ∧
        Blotto.Feasible (if player then 1 else (i.budget:ℝ))
          (PlayerSpecificRationalOutput.allocation
            (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).1) ∧
        (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
          PlayerSpecificFiniteDrawMeasuredSourceCost.work i
            p.accuracy.coinBits p.accuracy.scalarBits+
          PlayerSpecificRationalFiniteOutputPolynomial.outputWork i
            p.accuracy.scalarBits p.accuracy.outputBits := by
  obtain ⟨x,hx,hdraw⟩:=PlayerSpecificFiniteSamplerMeasuredSourceJoin.accepted_draws
    i epsilon he p hp
  refine ⟨x,hx,?_⟩
  intro player bits
  obtain ⟨hv,hbudget,hcost⟩:=hdraw player bits
  exact ⟨hv,hbudget,hcost.trans
    (PlayerSpecificRationalFiniteOutputPolynomial.finite_output_bound i
      p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits)⟩

end Blotto.PlayerSpecificFiniteSamplerOutputPolynomial
