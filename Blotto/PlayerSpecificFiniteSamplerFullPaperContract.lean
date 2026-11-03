import Blotto.PlayerSpecificFiniteSamplerCostEnvelope
import Blotto.PlayerSpecificFiniteSamplerMeasuredPaperContract
import Blotto.PlayerSpecificRealAlgorithm

/-! The same public finite-bit sampler has polynomial preparation, packet
work and random bits, budget-feasible outputs, independent players and
epsilon-Nash laws against every continuous deviation. The augmented
real-RAM exact algorithm is retained through its actual entry contract. -/
namespace Blotto.PlayerSpecificFiniteSamplerFullPaperContract
open MeasureTheory PlayerSpecificFiniteSampler PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem finite_bit_contract :
    ∃ C d Cbits dbits : ℕ,
      ∀ {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (_he : 0<epsilon)
        (p : Prepared N)
        (_hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p),
        (∀ (player : Bool) (bits : Fin (bitCount p) → Bool),
          (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2+
            (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
              C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
                rationalWordWidth epsilon+1)^d) ∧
        bitCount p≤Cbits*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
          rationalWordWidth epsilon+1)^dbits ∧
        Supported 1 (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true) ∧
        Supported (i.budget:ℝ) (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false) ∧
        regret i.valuesA.values 1
          (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)
          (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)≤(epsilon:ℝ) ∧
        regret i.valuesB.values (i.budget:ℝ)
          (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)
          (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)≤(epsilon:ℝ) ∧
        (PlayerSpecificFiniteSamplerMeasuredPaperContract.joint p :
          Measure (Allocation N × Allocation N))=
          (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true : Measure (Allocation N)).prod
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false : Measure (Allocation N)) ∧
        (∀ y : Allocation N,Blotto.Feasible 1 y →
          purePayoff i.valuesA.values y
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)≤
          expected i.valuesA.values
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)+(epsilon:ℝ)) ∧
        (∀ y : Allocation N,Blotto.Feasible (i.budget:ℝ) y →
          purePayoff i.valuesB.values y
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)≤
          expected i.valuesB.values
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)+(epsilon:ℝ)) := by
  obtain ⟨C,d,hcost⟩ := PlayerSpecificFiniteSamplerCostEnvelope.accepted_cost
  obtain ⟨Cbits,dbits,hbits⟩ := PlayerSpecificFiniteSamplerCostEnvelope.accepted_random_bits
  refine ⟨C,d,Cbits,dbits,?_⟩
  intro N i epsilon he p hp
  have hpaper := PlayerSpecificFiniteSamplerMeasuredPaperContract.accepted_contract
    i epsilon he p hp
  have hcontinuous := PlayerSpecificFiniteSamplerMeasuredPaperContract.all_continuous_deviations
    i epsilon he p hp
  exact ⟨hcost i epsilon he p hp,
    hbits i epsilon he p hp,
    hpaper.2.2.1,hpaper.2.2.2.1,hpaper.2.2.2.2.1,
    hpaper.2.2.2.2.2.1,hpaper.2.2.2.2.2.2,
    hcontinuous.1,hcontinuous.2⟩

end Blotto.PlayerSpecificFiniteSamplerFullPaperContract
