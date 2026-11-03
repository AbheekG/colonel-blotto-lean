import Blotto.BinaryFourSpecSampler
import Blotto.RationalFourSpecMachine
import Blotto.WordMappedIndexedRefinement
import Blotto.WordMachineLowerLeaf

/-! The native unsorted four-spec continuation accepts its caller's shared
cap and fixed outer/scalar blocks, retaining exact syntactic fallback. -/

namespace Blotto.BinaryFourSpecFixed
open BinaryRationalNormalization BinaryRationalEncoding BinaryFourSpecSampler

def sample (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord :=
  let row := BinaryFourSampler.fixedSample (orderedInput input) (orderedInput_canonical input hC) (orderedInput_admissible input hC hAd) K N outer scalar bits
  FixedArrayTable.ofFn (fun j => row.read (permutation input j))

theorem sample_value (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin 4) :
    value ((sample input hC hAd K N outer scalar bits).read j) = source.fixedSample K N outer scalar bits j := by
  simp only [sample,FixedArrayTable.read_ofFn]
  rw [BinaryFourSampler.fixedSample_value _ source.input _ (orderedInput_refines input source hC hr),permutation_refines input source hC hr]
  unfold RationalFourSpec.fixedSample RationalFourSpec.fallback RationalFourSpec.machine WordStateMachine.output
  rw [WordMappedIndexedRefinement.run_refines,WordStateMachine.mapped_chooseLeaf]
  unfold WordMappedIndexedRefinement.mapResult RationalFourInput.fixedSample
  simp only [WordStateMachine.output]
  cases hs : ((source.input.machine K outer scalar).run N (source.input.start K outer scalar) bits).1 with
  | none => exact (BinaryTerminalProfileCompiler.permutation_value source.permutation _ j).symm
  | some row => exact (BinaryTerminalProfileCompiler.permutation_value source.permutation row j).symm

theorem sample_canonical (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : ∀ j, CanonicalWord ((sample input hC hAd K N outer scalar bits).read j) := by
  intro j
  simp only [sample,FixedArrayTable.read_ofFn]
  exact BinaryFourSampler.fixedSample_canonical _ _ _ K N outer scalar bits _

end Blotto.BinaryFourSpecFixed
