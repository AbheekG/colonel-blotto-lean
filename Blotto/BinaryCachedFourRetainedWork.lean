import Blotto.BinaryFourSpecRetainedWork
import Blotto.BinaryReflectedCachedTerminalInput
import Blotto.BinaryCachedFourBranchWork

/-! Actual cached mixed-three original PRG fields instantiate the complete
retained four-variable producer in both regimes. Sorting, guard, actual small
setup reuse, fixed/scheduled draw, deterministic fallback and original-order
restoration preserve the old row and law. Original request fields derive the
primitive envelope; the general-n runner and complete model remain separate. -/

namespace Blotto.BinaryCachedFourRetainedWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGroupInputs
open BinaryCachedFourBranchWork BinaryCachedFourParameterWork BinaryCachedThreeDescriptorWork
open BinaryCachedTerminalPreparation BinaryCachedGroupInputHeight BinaryPRGResourceWork BinaryPRGTerminalWork

def fixedSample (checked : Checked) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FixedArrayTable 4 SignedWord × ℕ :=
  BinaryFourSpecRetainedWork.fixedSampleWithWork (mixedFour checked.input) (mixedFour_canonical checked.input checked.canonical)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible) K N outer scalar bits

theorem fixedSample_state (checked : Checked) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample checked K N outer scalar bits).1 =
      BinaryGroupSamplers.mixedSample checked.input checked.canonical checked.admissible (Or.inr rfl) K N outer scalar bits := by
  rw [fixedSample,BinaryFourSpecRetainedWork.fixedSampleWithWork_state]
  rfl

theorem fixedSample_bound (checked : Checked) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSample checked K N outer scalar bits).2 ≤ BinaryFourSpecRetainedWork.fixedBound s K N := by
  obtain ⟨source,hr⟩ := checked.admissible
  exact BinaryFourSpecRetainedWork.fixedSampleWithWork_bound _ source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible)
    s hs (source_four_heights checked.input source hr s hH) K N outer scalar bits

def sample (checked : Checked) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  BinaryFourSpecRetainedWork.sampleWithWork (mixedFour checked.input) (mixedFour_canonical checked.input checked.canonical)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible) K bits

theorem sample_bound (checked : Checked) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : (sample checked K bits).2 ≤ BinaryFourSpecRetainedWork.bound s K := by
  obtain ⟨source,hr⟩ := checked.admissible
  exact BinaryFourSpecRetainedWork.sampleWithWork_bound _ source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible)
    s hs (source_four_heights checked.input source hr s hH) K bits

def setupCache (checked : Checked) : BinaryReflectedSetupCache.Prepared checked.ordered :=
  BinaryReflectedSetupCache.prepareCache checked.ordered checked.ordered_canonical

theorem setupCache_bound (checked : Checked) (hSmall : ¬BinaryFourParentCompiler.gluingCase checked.ordered = true)
    (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s) : (setupCache checked).prefixWork ≤ BinaryReflectedSetupCache.bound s := by
  obtain ⟨source,hr⟩ := checked.admissible
  have hRef := BinaryFourSpecSampler.orderedInput_refines (mixedFour checked.input) source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
  have hCase := lt_of_not_ge (fun h => hSmall ((BinaryFourParentCompiler.gluingCase_iff checked.ordered source.fourInput.input
    checked.ordered_canonical hRef).mpr h))
  exact BinaryReflectedSetupCache.prepareCache_bound _ source.fourInput.input checked.ordered_canonical hRef hCase s hs
    (source_four_heights checked.input source hr s hH).input

theorem cached_fixedSample_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (K M : ℕ) (outer scalar : Fin K → Bool) (choice : Fin M → Bool) :
    (fixedSample (cached request rich N bits state h hCount selected hPivot) K M outer scalar choice).2 ≤
      BinaryFourSpecRetainedWork.fixedBound (inputHeight request) K M :=
  fixedSample_bound _ _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot) K M outer scalar choice

theorem cached_sample_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (K : ℕ) (choice : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    (sample (cached request rich N bits state h hCount selected hPivot) K choice).2 ≤ BinaryFourSpecRetainedWork.bound (inputHeight request) K :=
  sample_bound _ _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot) K choice

theorem cached_setupCache_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (hSmall : ¬BinaryFourParentCompiler.gluingCase (cached request rich N bits state h hCount selected hPivot).ordered = true) :
    (setupCache (cached request rich N bits state h hCount selected hPivot)).prefixWork ≤ BinaryReflectedSetupCache.bound (inputHeight request) :=
  setupCache_bound _ hSmall _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot)

def runIndexed (checked : Checked) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  BinaryFourSpecRetainedWork.runIndexedWithWork (mixedFour checked.input) (mixedFour_canonical checked.input checked.canonical)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible) K N outer scalar bits pos hp

theorem runIndexed_state (checked : Checked) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexed checked K N outer scalar bits pos hp).1 =
      BinaryGroupPartialRun.mixedRun checked.input checked.canonical checked.admissible (Or.inr rfl) K N outer scalar bits pos hp := by
  rw [runIndexed,BinaryFourSpecRetainedWork.runIndexedWithWork_state]
  rfl

theorem runIndexed_bound (checked : Checked) (s : ℕ) (hs : 2 ≤ s) (hH : MixedHeights checked.input s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexed checked K N outer scalar bits pos hp).2 ≤ BinaryFourSpecRetainedWork.runBound s K (N - pos) := by
  obtain ⟨source,hr⟩ := checked.admissible
  exact BinaryFourSpecRetainedWork.runIndexedWithWork_bound _ source.fourInput
    (mixedFour_canonical checked.input checked.canonical) (mixedFour_refines checked.input source hr)
    (BinaryGroupSamplers.mixedFour_admissible checked.input checked.canonical checked.admissible)
    s hs (source_four_heights checked.input source hr s hH) K N outer scalar bits pos hp

theorem cached_runIndexed_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (hCount : (prepare (terminalInput request rich state)).count = 3) (selected : Fin n)
    (hPivot : (prepare (terminalInput request rich state)).pivot = some selected)
    (K M : ℕ) (outer scalar : Fin K → Bool) (choice : Fin M → Bool) (pos : ℕ) (hp : pos ≤ M) :
    (runIndexed (cached request rich N bits state h hCount selected hPivot) K M outer scalar choice pos hp).2 ≤
      BinaryFourSpecRetainedWork.runBound (inputHeight request) K (M - pos) :=
  runIndexed_bound _ _ (inputHeight_two request) (cached_heights request rich N bits state h hCount selected hPivot) K M outer scalar choice pos hp

end Blotto.BinaryCachedFourRetainedWork
