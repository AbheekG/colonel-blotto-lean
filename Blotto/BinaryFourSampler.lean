import Blotto.BinaryFourAdmissibility
import Blotto.BinarySmallRootSample
import Blotto.BinaryGluingSampler
import Blotto.RationalFourBranchRun

/-! The native four-variable sampler executes both original branches from six
stored Boolean input words. The exact equality guard, shared cap, selected
continuations and lower-leaf exhaustion fallback preserve the original whole
law, canonical allocations and hard original budget. Full model prices and
input recognition remain separate, with the original input scope retained. -/

namespace Blotto.BinaryFourSampler
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryFourAdmissibility

theorem source_small_fixed (source : RationalFourInput) (hCase : source.w < (1-source.p)*source.ell)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    source.fixedSample K N outer scalar bits = source.smallFixedSample hCase K N outer scalar bits := by
  unfold RationalFourInput.fixedSample RationalFourInput.smallFixedSample WordStateMachine.output
  rw [WordStateMachine.run_eq_numeric,WordStateMachine.runNumeric]
  unfold RationalFourInput.start
  have hn : ¬(1-source.p)*source.ell ≤ source.w := not_le.mpr hCase
  rw [dite_eq_right hn]
  have he := source.small_runIndexed hCase K N outer scalar bits (.state BinaryState.start) 0 (Nat.zero_le N)
  simp only [WordCursor.mapState] at he
  rw [he]
  rw [← WordStateMachine.runNumeric,← WordStateMachine.run_eq_numeric,source.small_fallback hCase K outer scalar]

def fixedSample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord :=
  if hGuard : BinaryFourParentCompiler.gluingCase input=true then
    BinaryGluingSampler.fixedSample input hC (gluing_guard input hC hAd hGuard) K N scalar bits
  else BinarySmallRootSample.fixedSample input hC (small_guard input hC hAd hGuard) K N outer scalar bits

theorem fixedSample_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin 4) :
    value ((fixedSample input hC hAd K N outer scalar bits).read j) = source.fixedSample K N outer scalar bits j := by
  unfold fixedSample
  split
  · rename_i hg
    exact BinaryGluingSampler.fixedSample_value input source hC _ hr
      ((BinaryFourParentCompiler.gluingCase_iff input source hC hr).mp hg) K N outer scalar bits j
  · rename_i hg
    have hs := lt_of_not_ge (fun h => hg ((BinaryFourParentCompiler.gluingCase_iff input source hC hr).mpr h))
    rw [source_small_fixed source hs K N outer scalar bits]
    exact BinarySmallRootSample.fixedSample_value input source hC hr hs _ K N outer scalar bits j

theorem fixedSample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : ∀ j, CanonicalWord ((fixedSample input hC hAd K N outer scalar bits).read j) := by
  unfold fixedSample
  split
  · exact BinaryGluingSampler.fixedSample_canonical input hC _ K N scalar bits
  · exact BinarySmallRootSample.fixedSample_canonical input hC _ K N outer scalar bits

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord :=
  let inner := firstBitBlock (RationalFourInput.innerBitBudget K) K bits
  let outer := secondBitBlock (RationalFourInput.innerBitBudget K) K bits
  fixedSample input hC hAd K (RationalFourInput.coinBitBudget K) outer
    (secondBitBlock (RationalFourInput.coinBitBudget K) K inner)
    (firstBitBlock (RationalFourInput.coinBitBudget K) K inner)

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) (j : Fin 4) :
    value ((sample input hC hAd K bits).read j) = source.sample K bits j :=
  fixedSample_value input source hC hr hAd K _ _ _ _ j

theorem sample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : ∀ j, CanonicalWord ((sample input hC hAd K bits).read j) :=
  fixedSample_canonical input hC hAd K _ _ _ _

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) := by
  have he : (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) = fun j => (source.sample K bits j : ℝ) := by
    funext j
    rw [sample_value input source hC hr hAd]
  rw [he]
  exact source.sample_fullBudget K bits

noncomputable def sampleLaw (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalFourInput.sampleBitBudget K)).map (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) : sampleLaw input hC hAd K = source.sampleLaw K := by
  unfold sampleLaw RationalFourInput.sampleLaw
  congr 1
  funext bits j
  rw [sample_value input source hC hr hAd]

theorem sampleLaw_CDF_error (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) source.real.law (5/(2*(2:ℝ)^K)) := by
  rw [sampleLaw_eq input source hC hr hAd]
  exact source.sampleLaw_CDF_error K

end Blotto.BinaryFourSampler
