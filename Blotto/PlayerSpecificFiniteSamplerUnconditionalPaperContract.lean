import Blotto.PlayerSpecificFiniteSamplerFullPaperContract

/-! The finite-bit paper theorem without a supplied accepted preparation.
Exact parameter completeness produces that preparation whenever the paper's
positive parameter pair exists, and all guarantees concern that same result. -/
namespace Blotto.PlayerSpecificFiniteSamplerUnconditionalPaperContract
open MeasureTheory PlayerSpecificFiniteSampler PlayerSpecificRationalTrace
set_option autoImplicit false

theorem accepted_exists {N : ℕ} (i : RationalPlayerSpecificInput N)
    (epsilon : ℚ) (he : 0<epsilon)
    (hvalid : ∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values
        i.valuesB.values (i.budget:ℝ) gamma sigma) :
    ∃ p : Prepared N,
      (PlayerSpecificFiniteSamplerMeasuredExecution.prepare i epsilon).1=some p := by
  have hn : PlayerSpecificFiniteSampler.prepare i epsilon≠none := by
    intro hnone
    exact ((PlayerSpecificFiniteSampler.rejection_iff i epsilon).mp hnone) hvalid
  cases hp : PlayerSpecificFiniteSampler.prepare i epsilon with
  | none => exact False.elim (hn hp)
  | some p =>
    refine ⟨p,?_⟩
    rw [PlayerSpecificFiniteSamplerMeasuredExecution.prepare_value i epsilon he]
    exact hp

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
  obtain ⟨C,d,Cbits,dbits,hcontract⟩ :=
    PlayerSpecificFiniteSamplerFullPaperContract.finite_bit_contract
  refine ⟨C,d,Cbits,dbits,?_⟩
  intro N i epsilon he hvalid
  obtain ⟨p,hp⟩ := accepted_exists i epsilon he hvalid
  exact ⟨p,hp,hcontract i epsilon he p hp⟩

end Blotto.PlayerSpecificFiniteSamplerUnconditionalPaperContract
