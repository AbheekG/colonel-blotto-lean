import Blotto.BinaryReflectedSerialRun
import Blotto.BinaryTerminalFallback
import Blotto.RationalFourReflectedProgram

/-! Actual Boolean reflected output uses the exact source lower-leaf fallback
on either resource or categorical exhaustion. Fixed outer/scalar blocks remain
separate from the shared resource/categorical cap. Every path spends the original
budget and stays in its original coordinate box. -/

namespace Blotto.BinaryReflectedOutput
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedSerialRun

def fixedSample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord :=
  match (run input hC hAd K N outer scalar bits).1 with
  | some row => row
  | none => BinaryTerminalFallback.sample input hC hAd K outer scalar

theorem fixedSample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((fixedSample input hC hAd K N outer scalar bits).read j) := by
  unfold fixedSample
  split
  · rename_i row hs
    exact run_canonical input hC hAd K N outer scalar bits row hs
  · exact BinaryTerminalFallback.sample_canonical input hC hAd K outer scalar

theorem fixedSample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ)) := by
  unfold fixedSample
  split
  · rename_i row hs
    exact run_fullBudget input source hC hr hCase hAd K N outer scalar bits row hs
  · exact BinaryTerminalFallback.sample_fullBudget input source hC hAd hr hCase K outer scalar

theorem fixedSample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ)) := by
  unfold fixedSample
  split
  · rename_i row hs
    exact run_inBox input source hC hr hCase hAd K N outer scalar bits row hs
  · exact BinaryTerminalFallback.sample_inBox input source hC hAd hr hCase K outer scalar

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord :=
  let inner := firstBitBlock (RationalNestedResourceSystem.innerBitBudget K) K bits
  let outer := secondBitBlock (RationalNestedResourceSystem.innerBitBudget K) K bits
  fixedSample input hC hAd K (RationalNestedResourceSystem.coinBitBudget K) outer
    (secondBitBlock (RationalNestedResourceSystem.coinBitBudget K) K inner)
    (firstBitBlock (RationalNestedResourceSystem.coinBitBudget K) K inner)

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) :=
  fixedSample_fullBudget input source hC hr hCase hAd K _ _ _ _

theorem sample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalNestedResourceSystem.sampleBitBudget K) → Bool) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)] (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) :=
  fixedSample_inBox input source hC hr hCase hAd K _ _ _ _

end Blotto.BinaryReflectedOutput
