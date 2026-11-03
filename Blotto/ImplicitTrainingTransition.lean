import Blotto.SizedImplicitSampler
import Blotto.PreparedRationalTransition

/-! Native rational training observations draw two whole implicit allocations
and one value-weighted field from separate fixed seed blocks. Exact conditional
kernel semantics and all-test errors are derived. The Gibbs/history convergence
identification and continuous output/compiler costs remain separate. -/

namespace Blotto.ImplicitTrainingTransition
open ImplicitLeafCounts

abbrev Observation (m : ℕ) := PreparedRationalTransition.Observation m

def bitBudget {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ) : ℕ :=
  first.bitBudget epsilonFirst + second.bitBudget epsilonSecond + values.attempt.bitBudget K

def sample {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ)
    (bits : Fin (bitBudget first second values epsilonFirst epsilonSecond K) → Bool) : Observation m :=
  let seed : Fin (first.bitBudget epsilonFirst + (second.bitBudget epsilonSecond + values.attempt.bitBudget K)) → Bool :=
    fun j => bits (j.cast (by unfold bitBudget; omega))
  let firstBits := firstBitBlock (first.bitBudget epsilonFirst) (second.bitBudget epsilonSecond + values.attempt.bitBudget K) seed
  let rest := secondBitBlock (first.bitBudget epsilonFirst) (second.bitBudget epsilonSecond + values.attempt.bitBudget K) seed
  (first.sample epsilonFirst firstBits,
    second.sample epsilonSecond (firstBitBlock (second.bitBudget epsilonSecond) (values.attempt.bitBudget K) rest),
    PreparedProductTransition.fieldSample values K (secondBitBlock (second.bitBudget epsilonSecond) (values.attempt.bitBudget K) rest))

theorem sample_feasible {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond) (K : ℕ)
    (bits : Fin (bitBudget first second values epsilonFirst epsilonSecond K) → Bool) :
    Feasible (first.budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K bits).1 field : ℝ)) ∧
      Feasible (second.budget : ℝ) (fun field => ((sample first second values epsilonFirst epsilonSecond K bits).2.1 field : ℝ)) :=
  ⟨first.sample_feasible epsilonFirst hFirst _, second.sample_feasible epsilonSecond hSecond _⟩

noncomputable def actualKernel {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ) : BoundedExpectationKernel (Observation m) :=
  (first.nativeKernel epsilonFirst).bind (fun rowFirst => (second.nativeKernel epsilonSecond).bind
    (fun rowSecond => (PreparedProductTransition.fieldNativeKernel values K).map (fun field => (rowFirst, rowSecond, field))))

noncomputable def idealKernel {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m) :
    BoundedExpectationKernel (Observation m) :=
  first.targetKernel.bind (fun rowFirst => second.targetKernel.bind
    (fun rowSecond => (PreparedProductTransition.fieldIdealKernel values).map (fun field => (rowFirst, rowSecond, field))))

theorem sample_mean {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (K : ℕ) (test : Observation m → ℝ) :
    (fairBitKernel (bitBudget first second values epsilonFirst epsilonSecond K)).mean
      (fun bits => test (sample first second values epsilonFirst epsilonSecond K bits)) =
      (actualKernel first second values epsilonFirst epsilonSecond K).mean test := by
  have hCast := fairBitKernel_cast
    (first.bitBudget epsilonFirst + (second.bitBudget epsilonSecond + values.attempt.bitBudget K))
    (bitBudget first second values epsilonFirst epsilonSecond K) (by unfold bitBudget; omega)
    (fun bits => test (sample first second values epsilonFirst epsilonSecond K bits))
  apply hCast.symm.trans
  have hBlocks := fairBitKernel_blocks (first.bitBudget epsilonFirst) (second.bitBudget epsilonSecond + values.attempt.bitBudget K)
    (fun firstBits rest => test (first.sample epsilonFirst firstBits,
      second.sample epsilonSecond (firstBitBlock (second.bitBudget epsilonSecond) (values.attempt.bitBudget K) rest),
      PreparedProductTransition.fieldSample values K (secondBitBlock (second.bitBudget epsilonSecond) (values.attempt.bitBudget K) rest)))
  apply hBlocks.trans
  apply congrArg (fairBitKernel (first.bitBudget epsilonFirst)).mean
  funext firstBits
  exact fairBitKernel_blocks (second.bitBudget epsilonSecond) (values.attempt.bitBudget K)
    (fun secondBits fieldBits => test (first.sample epsilonFirst firstBits, second.sample epsilonSecond secondBits,
      PreparedProductTransition.fieldSample values K fieldBits))

theorem kernel_close {m : ℕ} (first second : SizedImplicitSampler m) (values : RationalFieldSelector m)
    (epsilonFirst epsilonSecond : ℚ) (hFirst : 0 < epsilonFirst) (hSecond : 0 < epsilonSecond) (K : ℕ) :
    (actualKernel first second values epsilonFirst epsilonSecond K).Close (idealKernel first second values)
      ((epsilonFirst : ℝ) + (epsilonSecond : ℝ) + 1 / (2 : ℝ) ^ K) := by
  have hField := PreparedProductTransition.fieldKernel_close values K
  have hNext : ∀ rowFirst : Fin m → ℚ,
      ((second.nativeKernel epsilonSecond).bind (fun rowSecond =>
        (PreparedProductTransition.fieldNativeKernel values K).map (fun field => (rowFirst, rowSecond, field)))).Close
      (second.targetKernel.bind (fun rowSecond =>
        (PreparedProductTransition.fieldIdealKernel values).map (fun field => (rowFirst, rowSecond, field))))
      ((epsilonSecond : ℝ) + 1 / (2 : ℝ) ^ K) := by
    intro rowFirst
    exact BoundedExpectationKernel.bind_close _ _ _ _ _ _ (second.nativeKernel_close epsilonSecond hSecond)
      (fun rowSecond => BoundedExpectationKernel.map_close _ _ (fun field => (rowFirst, rowSecond, field)) _ hField)
  have he := BoundedExpectationKernel.bind_close _ _ _ _ _ _ (first.nativeKernel_close epsilonFirst hFirst) hNext
  intro test hTest
  simpa only [actualKernel, idealKernel, add_assoc] using he test hTest

end Blotto.ImplicitTrainingTransition
