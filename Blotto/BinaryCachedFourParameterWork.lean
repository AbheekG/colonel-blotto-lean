import Blotto.BinaryCachedThreeDescriptorWork

/-! The mixed three-group/four-variable continuation derives its sorted six-
word input heights from cached original PRG data. Existing native parameter and
gluing producers then have their original work bounds without a supplied height
oracle. The distinct reflected small continuation remains separately required. -/

namespace Blotto.BinaryCachedFourParameterWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight BinaryCachedThreeDescriptorWork
open BinaryPRGResourceWork BinaryPRGTerminalWork

theorem source_four_heights (input : MixedInput 3) (source : RationalMixedGroupSpec 3)
    (hR : input.Refines source) (s : ℕ) (hH : MixedHeights input s) : source.fourInput.FieldsHeight s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change RationalHeight source.B s
    rw [← hR.1]; exact hH.1
  · intro j
    change RationalHeight (source.length j) s
    rw [← hR.2.1 j]; exact hH.2.1 j
  · change RationalHeight source.ell s
    rw [← hR.2.2.1]; exact hH.2.2.1
  · change RationalHeight source.p s
    rw [← hR.2.2.2]; exact hH.2.2.2

def parameterWork (input : MixedInput 3) : ℕ :=
  BinaryFourParameters.prepareWork (BinaryFourSpecSampler.orderedInput (mixedFour input))

def parameterBound (s : ℕ) : ℕ :=
  12 * (4 * s + 3) + 2048 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 12) + 12344

theorem parameterWork_bound (input : MixedInput 3) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s) :
    parameterWork input ≤ parameterBound s := by
  obtain ⟨source, hr⟩ := hAd
  have hFour := source_four_heights input source hr s hH
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour input) source.fourInput
    (mixedFour_canonical input hC) (mixedFour_refines input source hr)
  exact BinaryFourParameters.prepareWork_bound _ source.fourInput.input
    (BinaryFourSpecSampler.orderedInput_canonical _ (mixedFour_canonical input hC)) hR s hs hFour.input.environment

def gluingWork (input : MixedInput 3) : ℕ :=
  BinaryFourParentCompiler.descriptorWork (BinaryFourSpecSampler.orderedInput (mixedFour input))

theorem gluingWork_bound (input : MixedInput 3) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights input s)
    (hCase : BinaryFourParentCompiler.gluingCase (BinaryFourSpecSampler.orderedInput (mixedFour input)) = true) :
    gluingWork input ≤ BinaryFourParentCompiler.workBound s := by
  obtain ⟨source, hr⟩ := hAd
  have hFour := source_four_heights input source hr s hH
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour input) source.fourInput
    (mixedFour_canonical input hC) (mixedFour_refines input source hr)
  have hCanonical := BinaryFourSpecSampler.orderedInput_canonical _ (mixedFour_canonical input hC)
  have hActual := (BinaryFourParentCompiler.gluingCase_iff _ source.fourInput.input hCanonical hR).mp hCase
  exact BinaryFourParentCompiler.descriptorWork_bound _ source.fourInput.input hCanonical hR hActual s hs hFour.input

theorem cached_parameterWork_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected) :
    parameterWork (BinaryTerminalGroupInputs.castMixed hCount (prepare (terminalInput request rich state)).mixed) ≤
      parameterBound (inputHeight request) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  exact parameterWork_bound _ (mixed_canonical_forward hCount cached.mixed (cached.mixed_canonical hC selected hPivot))
    (mixed_admissible_forward hCount cached.mixed
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible cached hC hAd selected hPivot))
    _ (inputHeight_two request) (mixed_heights_cast hCount _ _ (cached_mixed_heights request rich N bits state h selected hPivot))

theorem cached_gluingWork_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool)
    (N : ℕ) (bits : Fin N → Bool) (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (hCase : BinaryFourParentCompiler.gluingCase (BinaryFourSpecSampler.orderedInput (mixedFour
      (BinaryTerminalGroupInputs.castMixed hCount (prepare (terminalInput request rich state)).mixed))) = true) :
    gluingWork (BinaryTerminalGroupInputs.castMixed hCount (prepare (terminalInput request rich state)).mixed) ≤
      BinaryFourParentCompiler.workBound (inputHeight request) := by
  let cached := prepare (terminalInput request rich state)
  have hC := terminal_canonical request rich state
  have hAd := terminal_admissible request rich N bits state h
  exact gluingWork_bound _ (mixed_canonical_forward hCount cached.mixed (cached.mixed_canonical hC selected hPivot))
    (mixed_admissible_forward hCount cached.mixed
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible cached hC hAd selected hPivot))
    _ (inputHeight_two request) (mixed_heights_cast hCount _ _ (cached_mixed_heights request rich N bits state h selected hPivot)) hCase

end Blotto.BinaryCachedFourParameterWork
