import Blotto.PlayerSpecificFiniteSamplerPreparationPolynomial
import Blotto.PlayerSpecificFiniteSamplerOutputPolynomial

/-! Preparation and rational-output polynomial work are joined on the
same accepted public sampler. The remaining finite algebraic draw work
is exposed explicitly for the terminal-core polynomial proof. -/
namespace Blotto.PlayerSpecificFiniteSamplerPartialPolynomial
open PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem accepted_work {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p)
    (player : Bool) (bits : Fin (bitCount p) → Bool) :
    (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2+
      (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
    PlayerSpecificFiniteSamplerPreparationPolynomial.originalPolynomial N
      (PlayerSpecificInitialPositivePrecision.inputSize i) epsilon+
    PlayerSpecificFiniteDrawMeasuredSourceCost.work i
      p.accuracy.coinBits p.accuracy.scalarBits+
    PlayerSpecificRationalFiniteOutputPolynomial.outputWork i
      p.accuracy.scalarBits p.accuracy.outputBits := by
  have hprepare:=PlayerSpecificFiniteSamplerPreparationPolynomial.accepted_original_source_cost
    i epsilon he p hp
  obtain ⟨x,hx,hdraw⟩:=PlayerSpecificFiniteSamplerOutputPolynomial.accepted_draws
    i epsilon he p hp
  have hcost:=(hdraw player bits).2.2
  have hsum:=Nat.add_le_add hprepare hcost
  simpa only [Nat.add_assoc] using hsum

end Blotto.PlayerSpecificFiniteSamplerPartialPolynomial
