import Blotto.BinaryReflectedCachedRun
import Blotto.BinaryReflectedLaw

/-! The cached native reflected sampler realizes the exact original whole law
with 5K+57 fair bits, original budgets on every path and the retained CDF bound.
Descriptions and full execution prices remain separate obligations. -/

namespace Blotto.BinaryReflectedCachedLaw
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedSerialRun

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord :=
  let inner := firstBitBlock (RationalNestedResourceSystem.innerBitBudget K) K bits
  let outer := secondBitBlock (RationalNestedResourceSystem.innerBitBudget K) K bits
  BinaryReflectedCachedRun.fixedSample input hC hAd K (RationalNestedResourceSystem.coinBitBudget K) outer
    (secondBitBlock (RationalNestedResourceSystem.coinBitBudget K) K inner)
    (firstBitBlock (RationalNestedResourceSystem.coinBitBudget K) K inner)

theorem sample_eq (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) :
    sample input hC hAd K bits = BinaryReflectedOutput.sample input hC hAd K bits := rfl

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) (j : Fin 4) :
    value ((sample input hC hAd K bits).read j) = source.reflectedSample hCase K bits j :=
  BinaryReflectedLaw.sample_value input source hC hr hCase hAd K bits j

theorem sample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) : ∀ j, CanonicalWord ((sample input hC hAd K bits).read j) :=
  BinaryReflectedOutput.fixedSample_canonical input hC hAd K _ _ _ _

theorem sample_feasible (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) :
    Feasible (source.B : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) :=
  fullBudget_feasible (BinaryReflectedOutput.sample_fullBudget input source hC hr hCase hAd K bits)

noncomputable def sampleLaw (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalNestedResourceSystem.sampleBitBudget K)).map (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K = source.reflectedSampleLaw hCase K :=
  BinaryReflectedLaw.sampleLaw_eq input source hC hr hCase hAd K

theorem sampleLaw_CDF_error (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) (source.real.reflectedZeroLaw (source.smallCase_real hCase)) (5/(2*(2:ℝ)^K)) :=
  BinaryReflectedLaw.sampleLaw_CDF_error input source hC hr hCase hAd K

end Blotto.BinaryReflectedCachedLaw
