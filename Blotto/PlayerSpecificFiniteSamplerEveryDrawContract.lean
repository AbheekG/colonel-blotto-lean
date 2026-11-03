import Blotto.PlayerSpecificFiniteSamplerUnconditionalPaperContract

/-! The finite-bit part of Theorem 2.6 with the budget stated for every draw.
`finite_bit_contract` states support almost surely; the accepted sampler in
fact returns a rational allocation within the budget on every bit string. -/
namespace Blotto.PlayerSpecificFiniteSamplerEveryDrawContract
open MeasureTheory PlayerSpecificFiniteSampler
set_option autoImplicit false

theorem every_draw_feasible {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon) (p : Prepared N)
    (hp : (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p)
    (player : Bool) (bits : Fin (bitCount p) → Bool) :
    Blotto.Feasible (if player then 1 else (i.budget:ℝ))
      (PlayerSpecificFiniteSamplerMeasuredPaperContract.sample p player bits) := by
  have hp' : PlayerSpecificFiniteSampler.prepare i epsilon=some p := by
    rw [← PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp
  obtain ⟨_,_,_,hdraw⟩ := PlayerSpecificFiniteSamplerContract.accepted_draws i epsilon p hp'
  rw [PlayerSpecificFiniteSamplerMeasuredPaperContract.sample_eq]
  exact (hdraw player bits).1

theorem finite_bit_contract :
    ∃ C d Cbits dbits : ℕ,
      ∀ {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (_he : 0<epsilon),
        (∃ gamma sigma,
          PlayerSpecificRecognition.ValidParameters i.valuesA.values
            i.valuesB.values (i.budget:ℝ) gamma sigma) →
        ∃ p : Prepared N,
          (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p ∧
          (∀ (player : Bool) (bits : Fin (bitCount p) → Bool),
            (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).2+
              (PlayerSpecificFiniteSamplerMeasuredExecution.draw p player bits).2≤
                C*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
                  rationalWordWidth epsilon+1)^d ∧
            Blotto.Feasible (if player then 1 else (i.budget:ℝ))
              (PlayerSpecificFiniteSamplerMeasuredPaperContract.sample p player bits)) ∧
          bitCount p≤Cbits*(N+PlayerSpecificInitialPositivePrecision.inputSize i+
            rationalWordWidth epsilon+1)^dbits ∧
          regret i.valuesA.values 1
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)≤(epsilon:ℝ) ∧
          regret i.valuesB.values (i.budget:ℝ)
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false)
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true)≤(epsilon:ℝ) ∧
          (PlayerSpecificFiniteSamplerMeasuredPaperContract.joint p :
            Measure (Allocation N × Allocation N))=
            (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p true : Measure (Allocation N)).prod
              (PlayerSpecificFiniteSamplerMeasuredPaperContract.law p false : Measure (Allocation N)) := by
  obtain ⟨C,d,Cbits,dbits,hcontract⟩ :=
    PlayerSpecificFiniteSamplerUnconditionalPaperContract.finite_bit_contract
  refine ⟨C,d,Cbits,dbits,?_⟩
  intro N i epsilon he hvalid
  obtain ⟨p,hp,hcost,hbits,_,_,hA,hB,hjoint,_⟩ := hcontract i epsilon he hvalid
  exact ⟨p,hp,fun player bits => ⟨hcost player bits,every_draw_feasible i epsilon he p hp player bits⟩,
    hbits,hA,hB,hjoint⟩

end Blotto.PlayerSpecificFiniteSamplerEveryDrawContract
