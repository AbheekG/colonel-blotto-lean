import Blotto.BinarySmallFixedPrimitiveWork
import Blotto.BinaryCachedFourSmallPrimitiveWork

/-! Actual cached original-game mixed-three data derive the complete small
fixed-draw primitive price, including the deterministic lower fallback. The
same original source heights instantiate fixed-cap and retained finite-bit
schedule bounds; no reached-height/descriptor/source oracle is supplied. -/

namespace Blotto.BinaryCachedFourSmallFixedWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight BinaryPRGResourceWork BinaryPRGTerminalWork

def fixedSample (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  BinarySmallFixedPrimitiveWork.fixedSampleWithWork checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h)
    K N outer scalar bits

theorem fixedSample_state (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample checked h K N outer scalar bits).1 = BinarySmallRootSample.fixedSample checked.ordered checked.ordered_canonical
      (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h) K N outer scalar bits :=
  BinarySmallFixedPrimitiveWork.fixedSampleWithWork_state _ _ _ K N outer scalar bits

theorem fixedSample_bound (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample checked h K N outer scalar bits).2 ≤ BinarySmallFixedPrimitiveWork.fixedBound s K N := by
  obtain ⟨source,hr⟩ := checked.admissible
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
  have hHeight := (source_four_heights checked.input source hr s hH).input
  have hCase := lt_of_not_ge (fun he => h ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
    checked.ordered_canonical hR).mpr he))
  exact BinarySmallFixedPrimitiveWork.fixedSampleWithWork_bound _ source.fourInput.input checked.ordered_canonical hR _ hCase s hs hHeight K N outer scalar bits

def sample (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  BinarySmallFixedPrimitiveWork.sampleWithWork checked.ordered checked.ordered_canonical
    (BinaryFourAdmissibility.small_guard checked.ordered checked.ordered_canonical checked.ordered_admissible h) K bits

theorem sample_bound (checked : Checked) (h : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) :
    (sample checked h K bits).2 ≤ BinarySmallFixedPrimitiveWork.bound s K := by
  obtain ⟨source,hr⟩ := checked.admissible
  have hR := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
  have hHeight := (source_four_heights checked.input source hr s hH).input
  have hCase := lt_of_not_ge (fun he => h ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
    checked.ordered_canonical hR).mpr he))
  exact BinarySmallFixedPrimitiveWork.sampleWithWork_bound _ source.fourInput.input checked.ordered_canonical hR _ hCase s hs hHeight K bits

theorem cached_fixedSample_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (hSmall : ¬BinaryFourParentCompiler.gluingCase (cached request rich N bits state h hCount selected hPivot).ordered = true)
    (K M : ℕ) (outer scalar : Fin K → Bool) (choice : Fin M → Bool) :
    (fixedSample (cached request rich N bits state h hCount selected hPivot) hSmall K M outer scalar choice).2 ≤
      BinarySmallFixedPrimitiveWork.fixedBound (inputHeight request) K M :=
  fixedSample_bound _ hSmall _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot)
    K M outer scalar choice

theorem cached_sample_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (hSmall : ¬BinaryFourParentCompiler.gluingCase (cached request rich N bits state h hCount selected hPivot).ordered = true)
    (K : ℕ) (choice : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) :
    (sample (cached request rich N bits state h hCount selected hPivot) hSmall K choice).2 ≤
      BinarySmallFixedPrimitiveWork.bound (inputHeight request) K :=
  sample_bound _ hSmall _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot) K choice

end Blotto.BinaryCachedFourSmallFixedWork
