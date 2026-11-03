import Blotto.BinarySegmentSampler
import Blotto.BinaryNestedSpecProfile
import Blotto.RationalNestedSpecProgram

/-! The complete nested-spec finite-bit sampler executes its actual stored
Boolean profile and independent categorical/midpoint blocks. Exact all-seed
refinement preserves the original full budget and 5/(2*2^K) marginal error.
Whole reflected-resource serial composition and full costs remain separate. -/

namespace Blotto.BinaryNestedSpecSample
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryNestedParameters BinaryNestedTerminalInput

def sample (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) : FixedArrayTable 3 SignedWord :=
  let outer := secondBitBlock (RationalNestedInput.conditionalBitBudget K) K bits
  let table := BinaryNestedSpecProfile.profile input K outer
  BinarySegmentSampler.flatSample table (source.profile K outer)
    (BinaryNestedSpecProfile.profile_canonical input h K outer) (BinaryNestedSpecProfile.profile_refines input source h hr K outer)
    0 (3*(17+K)) K (firstBitBlock (RationalNestedInput.conditionalBitBudget K) K bits)

theorem sample_canonical (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) : ∀ j, CanonicalWord ((sample input source h hr K bits).read j) :=
  BinarySegmentSampler.flatSample_canonical _ _ _ _ _ _ _ _

theorem sample_value (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) (j : Fin 3) :
    value ((sample input source h hr K bits).read j) = source.sample K bits j :=
  BinarySegmentSampler.flatSample_value _ _ _ _ _ _ _ _ j

theorem sample_fullBudget (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) :
    FullBudget (source.M : ℝ) (fun j => (value ((sample input source h hr K bits).read j) : ℝ)) := by
  have hValues : (fun j => (value ((sample input source h hr K bits).read j) : ℝ)) = fun j => (source.sample K bits j : ℝ) := by
    funext j; exact congrArg (fun q : ℚ => (q : ℝ)) (sample_value input source h hr K bits j)
  rw [hValues]
  exact source.sample_fullBudget K bits

noncomputable def sampleLaw (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) : Mixed 3 :=
  (fairBitLaw (RationalNestedInput.sampleBitBudget K)).map (fun bits j => (value ((sample input source h hr K bits).read j) : ℝ))

theorem sampleLaw_eq (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) : sampleLaw input source h hr K = source.sampleLaw K := by
  unfold sampleLaw RationalNestedSpec.sampleLaw
  congr 1
  funext bits j
  rw [sample_value]

theorem sampleLaw_CDF_error (input : Input) (source : RationalNestedSpec) (h : input.Canonical) (hr : InputRefinesSpec input source)
    (K : ℕ) : CDFClose (sampleLaw input source h hr K) source.real.law (5/(2*(2:ℝ)^K)) := by
  rw [sampleLaw_eq]
  exact source.sampleLaw_CDF_error K

end Blotto.BinaryNestedSpecSample
