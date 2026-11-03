import Blotto.BinaryFourSampler
import Blotto.RationalFourSpec
import Blotto.BinaryTerminalProfileCompiler

/-! Native three-comparison sorting and inverse coordinate restoration lift the
complete Boolean four sampler to the original unsorted positive-length scope.
The mixture coordinate remains fixed. Exact whole law and hard budgets transfer;
full compiler/input-recognition/runtime contracts remain separate. -/

namespace Blotto.BinaryFourSpecSampler
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding

structure Input where
  B : SignedWord
  length : FixedArrayTable 3 SignedWord
  ell : SignedWord
  p : SignedWord

def Input.Canonical (input : Input) : Prop := CanonicalWord input.B ∧ (∀ j, CanonicalWord (input.length.read j)) ∧
  CanonicalWord input.ell ∧ CanonicalWord input.p

def Input.Refines (input : Input) (source : RationalFourSpec) : Prop := value input.B = source.B ∧
  (∀ j, value (input.length.read j) = source.length j) ∧ value input.ell = source.ell ∧ value input.p = source.p

def Admissible (input : Input) : Prop := ∃ source : RationalFourSpec, input.Refines source

def comparePermutation (length : Fin 3 → SignedWord) (i j : Fin 3) : Equiv.Perm (Fin 3) :=
  if BinaryRationalArithmetic.lessEqual (length i) (length j) then Equiv.refl _ else Equiv.swap i j

def sortPermutation (length : Fin 3 → SignedWord) : Equiv.Perm (Fin 3) :=
  let p := comparePermutation length 0 1
  let M := fun j => length (p j)
  let q := comparePermutation M 1 2
  let N := fun j => M (q j)
  let r := comparePermutation N 0 1
  (r.trans q).trans p

theorem comparePermutation_refines (length : Fin 3 → SignedWord) (source : Fin 3 → ℚ)
    (hC : ∀ j, CanonicalWord (length j)) (hr : ∀ j, value (length j) = source j) (i j : Fin 3) :
    comparePermutation length i j = rationalComparePermutation source i j := by
  have he := BinaryRationalArithmetic.lessEqual_iff (length i) (length j) (hC i).1 (hC j).1
  rw [hr i,hr j] at he
  simp only [comparePermutation,rationalComparePermutation,he]

theorem sortPermutation_refines (length : Fin 3 → SignedWord) (source : Fin 3 → ℚ)
    (hC : ∀ j, CanonicalWord (length j)) (hr : ∀ j, value (length j) = source j) :
    sortPermutation length = rationalSortTriplePermutation source := by
  have hp := comparePermutation_refines length source hC hr 0 1
  have hq := comparePermutation_refines (fun j => length (comparePermutation length 0 1 j))
    (fun j => source (rationalComparePermutation source 0 1 j)) (fun j => hC _) (fun j => by rw [hr,hp]) 1 2
  have ht := comparePermutation_refines
    (fun j => length (comparePermutation length 0 1 (comparePermutation (fun j => length (comparePermutation length 0 1 j)) 1 2 j)))
    (fun j => source (rationalComparePermutation source 0 1 (rationalComparePermutation (fun j => source (rationalComparePermutation source 0 1 j)) 1 2 j)))
    (fun j => hC _) (fun j => by rw [hr,hq,hp]) 0 1
  unfold sortPermutation rationalSortTriplePermutation
  dsimp only
  rw [ht,hq,hp]

def orderedInput (input : Input) : BinaryFourParameters.Input :=
  let pi := sortPermutation input.length.read
  ⟨input.B,input.length.read (pi 0),input.length.read (pi 1),input.length.read (pi 2),input.ell,input.p⟩

theorem orderedInput_canonical (input : Input) (hC : input.Canonical) : (orderedInput input).Canonical :=
  ⟨hC.1,hC.2.1 _,hC.2.1 _,hC.2.1 _,hC.2.2.1,hC.2.2.2⟩

theorem orderedInput_refines (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) :
    (orderedInput input).Refines source.input := by
  have hp := sortPermutation_refines input.length.read source.length hC.2.1 hr.2.1
  refine ⟨hr.1,?_,?_,?_,hr.2.2.1,hr.2.2.2⟩
  all_goals change value (input.length.read (sortPermutation input.length.read _)) = _
  all_goals rw [hp,hr.2.1]
  all_goals rfl

theorem orderedInput_admissible (input : Input) (hC : input.Canonical) (hAd : Admissible input) :
    BinaryFourAdmissibility.Admissible (orderedInput input) := by
  obtain ⟨source,hr⟩ := hAd
  exact ⟨source.input,orderedInput_refines input source hC hr⟩

def permutation (input : Input) : Equiv.Perm (Fin 4) := (rationalPermutationWithLast (sortPermutation input.length.read)).symm

theorem permutation_refines (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) :
    permutation input = source.permutation := by
  rw [permutation,sortPermutation_refines input.length.read source.length hC.2.1 hr.2.1]
  rfl

def sample (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord :=
  let row := BinaryFourSampler.sample (orderedInput input) (orderedInput_canonical input hC) (orderedInput_admissible input hC hAd) K bits
  FixedArrayTable.ofFn (fun j => row.read (permutation input j))

theorem sample_value (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) (j : Fin 4) :
    value ((sample input hC hAd K bits).read j) = source.sample K bits j := by
  simp only [sample,FixedArrayTable.read_ofFn]
  rw [BinaryFourSampler.sample_value _ source.input _ (orderedInput_refines input source hC hr),permutation_refines input source hC hr]
  exact (BinaryTerminalProfileCompiler.permutation_value source.permutation (source.input.sample K bits) j).symm

theorem sample_canonical (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : ∀ j, CanonicalWord ((sample input hC hAd K bits).read j) := by
  intro j
  simp only [sample,FixedArrayTable.read_ofFn]
  exact BinaryFourSampler.sample_canonical _ _ _ K bits _

theorem sample_fullBudget (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) := by
  have he : (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) = fun j => (source.sample K bits j : ℝ) := by
    funext j
    rw [sample_value input source hC hr hAd]
  rw [he]
  exact source.sample_fullBudget K bits

noncomputable def sampleLaw (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalFourInput.sampleBitBudget K)).map (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K = source.sampleLaw K := by
  unfold sampleLaw RationalFourSpec.sampleLaw
  congr 1
  funext bits j
  rw [sample_value input source hC hr hAd]

theorem sampleLaw_CDF_error (input : Input) (source : RationalFourSpec) (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) source.real.law (5/(2*(2:ℝ)^K)) := by
  rw [sampleLaw_eq input source hC hr hAd]
  exact source.sampleLaw_CDF_error K

end Blotto.BinaryFourSpecSampler
