import Blotto.ExactSizedDraw
import Blotto.ImplicitTrainingTransition

/-! Replacing the two stored draws by exact native implementations preserves
the actual disjoint seed layout and whole training observation. This transport
interface acquires an implementation only from concrete derived constructors. -/

namespace Blotto.ExactSizedTrainingTransition
open ImplicitLeafCounts

abbrev Observation (m : ℕ) := ImplicitTrainingTransition.Observation m

def bitBudget {m : ℕ} (first second : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ) : ℕ :=
  first.bitBudget epsilonFirst + second.bitBudget epsilonSecond + values.attempt.bitBudget K

def sample {m : ℕ} (first second : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ)
    (bits : Fin (bitBudget first second values epsilonFirst epsilonSecond K) → Bool) : Observation m :=
  let seed : Fin (first.bitBudget epsilonFirst + (second.bitBudget epsilonSecond + values.attempt.bitBudget K)) → Bool :=
    fun j => bits (j.cast (by unfold bitBudget; omega))
  let firstBits := firstBitBlock (first.bitBudget epsilonFirst) (second.bitBudget epsilonSecond + values.attempt.bitBudget K) seed
  let rest := secondBitBlock (first.bitBudget epsilonFirst) (second.bitBudget epsilonSecond + values.attempt.bitBudget K) seed
  (first.draw epsilonFirst firstBits,
    second.draw epsilonSecond (firstBitBlock (second.bitBudget epsilonSecond) (values.attempt.bitBudget K) rest),
    PreparedProductTransition.fieldSample values K (secondBitBlock (second.bitBudget epsilonSecond) (values.attempt.bitBudget K) rest))

theorem sample_refines {m : ℕ} (first second : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ)
    (bits : Fin (bitBudget first second values epsilonFirst epsilonSecond K) → Bool) :
    sample first second values epsilonFirst epsilonSecond K bits =
      ImplicitTrainingTransition.sample first.model second.model values epsilonFirst epsilonSecond K bits := by
  unfold sample ImplicitTrainingTransition.sample
  dsimp only [ExactSizedDraw.bitBudget]
  rw [first.refines, second.refines]
  rfl

theorem sample_feasible {m : ℕ} (first second : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond) (K : ℕ)
    (bits : Fin (bitBudget first second values epsilonFirst epsilonSecond K) → Bool) :
    Feasible (first.budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K bits).1 field : ℝ)) ∧
      Feasible (second.budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K bits).2.1 field : ℝ)) := by
  rw [sample_refines]
  exact ImplicitTrainingTransition.sample_feasible first.model second.model values epsilonFirst epsilonSecond hFirst hSecond K bits

theorem sample_mean {m : ℕ} (first second : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ) (test : Observation m → ℝ) :
    (fairBitKernel (bitBudget first second values epsilonFirst epsilonSecond K)).mean
      (fun bits => test (sample first second values epsilonFirst epsilonSecond K bits)) =
      (ImplicitTrainingTransition.actualKernel first.model second.model values epsilonFirst epsilonSecond K).mean test := by
  simp_rw [sample_refines]
  exact ImplicitTrainingTransition.sample_mean first.model second.model values epsilonFirst epsilonSecond K test

theorem kernel_close {m : ℕ} (first second : ExactSizedDraw m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond) (K : ℕ) :
    ((fairBitKernel (bitBudget first second values epsilonFirst epsilonSecond K)).map
      (sample first second values epsilonFirst epsilonSecond K)).Close
      (ImplicitTrainingTransition.idealKernel first.model second.model values)
      ((epsilonFirst : ℝ) + (epsilonSecond : ℝ) + 1 / (2 : ℝ) ^ K) := by
  intro test hTest
  change |(fairBitKernel _).mean (fun bits => test (sample first second values epsilonFirst epsilonSecond K bits)) - _| ≤ _
  rw [sample_mean]
  exact ImplicitTrainingTransition.kernel_close first.model second.model values epsilonFirst epsilonSecond hFirst hSecond K test hTest

end Blotto.ExactSizedTrainingTransition
