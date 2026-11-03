import Blotto.BinaryReflectedRunRefinement
import Blotto.BinaryReflectedOutput

/-! Exact native serial execution and the exact deterministic fallback transfer
the original whole reflected law and 5/(2*2^K) marginal error. The native entry
point uses stored words and erased admissibility only; full prices are separate. -/

namespace Blotto.BinaryReflectedLaw
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedSerialRun BinaryReflectedSerialValue

theorem fixedSample_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin 4) :
    value ((BinaryReflectedOutput.fixedSample input hC hAd K N outer scalar bits).read j) =
      (RationalAffineAllocation.reflectAppend source.originalLengths).value
        ((source.reflectedResourceSystem hCase).fixedSample K N outer scalar bits) j := by
  have he := congrArg Prod.fst (BinaryReflectedRunRefinement.run_refines input source hC hr hCase hAd K N outer scalar bits)
  change (run input hC hAd K N outer scalar bits).1.map sourceRow =
    ((((source.reflectedResourceSystem hCase).machine K outer scalar).run N
      (source.reflectedResourceSystem hCase).samplingStart bits).1.map
        (RationalAffineAllocation.reflectAppend source.originalLengths).value) at he
  unfold BinaryReflectedOutput.fixedSample RationalNestedResourceSystem.fixedSample WordStateMachine.output
  cases hNative : (run input hC hAd K N outer scalar bits).1 with
  | none =>
    rw [hNative,Option.map_none] at he
    have hNone := Option.map_eq_none_iff.mp he.symm
    rw [hNone]
    exact BinaryTerminalFallback.sample_value input source hC hAd hr hCase K outer scalar j
  | some row =>
    rw [hNative,Option.map_some] at he
    cases hSource : (((source.reflectedResourceSystem hCase).machine K outer scalar).run N
      (source.reflectedResourceSystem hCase).samplingStart bits).1 with
    | none => rw [hSource,Option.map_none] at he; cases he
    | some allocation =>
      rw [hSource,Option.map_some] at he
      change value (row.read j) = _
      exact congrFun (Option.some.inj he) j

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) (j : Fin 4) :
    value ((BinaryReflectedOutput.sample input hC hAd K bits).read j) = source.reflectedSample hCase K bits j :=
  fixedSample_value input source hC hr hCase hAd K _ _ _ _ j

noncomputable def sampleLaw (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalNestedResourceSystem.sampleBitBudget K)).map
    (fun bits j => (value ((BinaryReflectedOutput.sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K = source.reflectedSampleLaw hCase K := by
  unfold sampleLaw RationalFourInput.reflectedSampleLaw
  congr 1
  funext bits j
  rw [sample_value input source hC hr hCase hAd]

theorem sampleLaw_CDF_error (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) (source.real.reflectedZeroLaw (source.smallCase_real hCase)) (5/(2*(2:ℝ)^K)) := by
  rw [sampleLaw_eq input source hC hr hCase hAd]
  exact source.reflectedSampleLaw_CDF_error hCase K

end Blotto.BinaryReflectedLaw
