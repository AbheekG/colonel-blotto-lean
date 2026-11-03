import Blotto.RationalFourProgram
import Blotto.RationalSortTriple
import Blotto.FourSpec

/-! Native four-variable inputs with unsorted positive group lengths.
Three rational comparisons normalize the input; the last mixture coordinate
stays fixed when allocations return to original order. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

structure RationalFourSpec where
  B : ℚ
  length : Fin 3 → ℚ
  ell : ℚ
  p : ℚ
  length_pos : ∀ j, 0 < length j
  length_le : ∀ j, length j ≤ B
  ell_pos : 0 < ell
  ell_le : ell ≤ B
  p_pos : 0 < p
  p_lt : p < 1
  balance : (∑ j, length j) + p * ell = 2 * B

namespace RationalFourSpec

noncomputable def real (i : RationalFourSpec) : FourSpec where
  B := i.B
  length := fun j => i.length j
  ell := i.ell
  p := i.p
  length_pos := fun j => by exact_mod_cast i.length_pos j
  length_le := fun j => by exact_mod_cast i.length_le j
  ell_pos := by exact_mod_cast i.ell_pos
  ell_le := by exact_mod_cast i.ell_le
  p_pos := by exact_mod_cast i.p_pos
  p_lt := by exact_mod_cast i.p_lt
  balance := by exact_mod_cast i.balance

def input (i : RationalFourSpec) : RationalFourInput where
  B := i.B
  u := rationalSortedTriple i.length 0
  v := rationalSortedTriple i.length 1
  w := rationalSortedTriple i.length 2
  ell := i.ell
  p := i.p
  u_pos := i.length_pos _
  uv := (rationalSortedTriple_ordered i.length).1
  vw := (rationalSortedTriple_ordered i.length).2
  ell_pos := i.ell_pos
  p_pos := i.p_pos
  p_lt := i.p_lt
  w_le := i.length_le _
  ell_le := i.ell_le
  balance := by
    have he := Equiv.sum_comp (rationalSortTriplePermutation i.length) i.length
    change (∑ j, rationalSortedTriple i.length j) = ∑ j, i.length j at he
    have hb := i.balance
    simp [Fin.sum_univ_succ] at he hb
    linarith

theorem input_real (i : RationalFourSpec) : i.input.real = i.real.input := by
  apply FourInput.eq_of_data
  · rfl
  · exact rationalSortedTriple_real i.length 0
  · exact rationalSortedTriple_real i.length 1
  · exact rationalSortedTriple_real i.length 2
  · rfl
  · rfl

def permutation (i : RationalFourSpec) : Equiv.Perm (Fin 4) :=
  (rationalPermutationWithLast (rationalSortTriplePermutation i.length)).symm

theorem permutation_real (i : RationalFourSpec) :
    i.permutation = (permutationWithLast (sortTriplePermutation i.real.length)).symm := by
  unfold permutation
  rw [rationalPermutationWithLast_real, rationalSortTriplePermutation_real]
  rfl

def machine (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    WordStateMachine (FourSamplingState i.input) (Fin 4 → ℚ) :=
  (i.input.machine K outerBits scalarBits).mapped (RationalAffineAllocation.permutation i.permutation).value

theorem machine_rank (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.machine K outerBits scalarBits).rank (i.input.start K outerBits scalarBits) ≤ 80 :=
  i.input.machine_rank K outerBits scalarBits

def sample (i : RationalFourSpec) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : Fin 4 → ℚ :=
  (RationalAffineAllocation.permutation i.permutation).value (i.input.sample K bits)

noncomputable def sampleLaw (i : RationalFourSpec) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalFourInput.sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ))

theorem sample_fullBudget (i : RationalFourSpec) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.sample K bits j : ℝ)) := by
  rw [sample, RationalAffineAllocation.value_real, RationalAffineAllocation.permutation_real]
  exact permuteAllocation_fullBudget i.permutation (i.input.sample_fullBudget K bits)

theorem sampleLaw_eq (i : RationalFourSpec) (K : ℕ) :
    i.sampleLaw K = permuteLaw i.permutation (i.input.sampleLaw K) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits j => (i.sample K bits j : ℝ))
    (fairBitLaw (RationalFourInput.sampleBitBudget K) : Measure (Fin (RationalFourInput.sampleBitBudget K) → Bool)) =
    Measure.map (permuteAllocation i.permutation) (Measure.map (fun bits j => (i.input.sample K bits j : ℝ))
      (fairBitLaw (RationalFourInput.sampleBitBudget K) : Measure (Fin (RationalFourInput.sampleBitBudget K) → Bool)))
  rw [Measure.map_map (measurable_permuteAllocation _) (measurable_of_countable _)]
  congr 1
  funext bits
  rw [sample, RationalAffineAllocation.value_real, RationalAffineAllocation.permutation_real]
  rfl

theorem sampleLaw_CDF_error (i : RationalFourSpec) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [i.sampleLaw_eq]
  have h := permuteLaw_CDFClose (i.input.sampleLaw_CDF_error K) i.permutation
  simpa only [i.input_real, i.permutation_real, FourSpec.law] using h

end RationalFourSpec
end Blotto
