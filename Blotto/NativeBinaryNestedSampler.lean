import Blotto.NativeBinarySegmentSampler
import Blotto.BinaryNestedSpecSample

/-! The native nested entry point takes stored input words and a valid-source
witness only in Prop. It never accepts or selects a semantic source as runtime
data. Exact equality transfers the original whole-output and law guarantees. -/

namespace Blotto.NativeBinaryNestedSampler
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryNestedParameters BinaryNestedTerminalInput

def Admissible (input : Input) : Prop := ∃ source : RationalNestedSpec, InputRefinesSpec input source

theorem profile_nonnegative (input : Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin K → Bool) : ∀ slot, 0 ≤ value ((BinaryNestedSpecProfile.profile input K bits).weight.read slot) := by
  obtain ⟨source,hr⟩ := hAd
  intro slot
  rw [(BinaryNestedSpecProfile.profile_refines input source hC hr K bits).1 slot]
  exact (source.profile K bits).nonnegative slot

def sample (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) : FixedArrayTable 3 SignedWord :=
  let outer := secondBitBlock (RationalNestedInput.conditionalBitBudget K) K bits
  NativeBinarySegmentSampler.flatSample (BinaryNestedSpecProfile.profile input K outer)
    (BinaryNestedSpecProfile.profile_canonical input hC K outer) (profile_nonnegative input hC hAd K outer)
    0 (3*(17+K)) K (firstBitBlock (RationalNestedInput.conditionalBitBudget K) K bits)

theorem sample_eq (input : Input) (hC : input.Canonical) (hAd : Admissible input) (source : RationalNestedSpec)
    (hr : InputRefinesSpec input source) (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) :
    sample input hC hAd K bits = BinaryNestedSpecSample.sample input source hC hr K bits := rfl

theorem sample_value (input : Input) (hC : input.Canonical) (hAd : Admissible input) (source : RationalNestedSpec)
    (hr : InputRefinesSpec input source) (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) (j : Fin 3) :
    value ((sample input hC hAd K bits).read j) = source.sample K bits j := by
  rw [sample_eq input hC hAd source hr]
  exact BinaryNestedSpecSample.sample_value input source hC hr K bits j

theorem sample_canonical (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) : ∀ j, CanonicalWord ((sample input hC hAd K bits).read j) :=
  NativeBinarySegmentSampler.flatSample_canonical _ _ _ _ _ _ _

theorem sample_fullBudget (input : Input) (hC : input.Canonical) (hAd : Admissible input) (source : RationalNestedSpec)
    (hr : InputRefinesSpec input source) (K : ℕ) (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) :
    FullBudget (source.M : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) := by
  rw [sample_eq input hC hAd source hr]
  exact BinaryNestedSpecSample.sample_fullBudget input source hC hr K bits

noncomputable def sampleLaw (input : Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 3 :=
  (fairBitLaw (RationalNestedInput.sampleBitBudget K)).map (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : Input) (hC : input.Canonical) (hAd : Admissible input) (source : RationalNestedSpec)
    (hr : InputRefinesSpec input source) (K : ℕ) : sampleLaw input hC hAd K = source.sampleLaw K := by
  unfold sampleLaw RationalNestedSpec.sampleLaw
  congr 1
  funext bits j
  rw [sample_value input hC hAd source hr]

theorem sampleLaw_CDF_error (input : Input) (hC : input.Canonical) (hAd : Admissible input) (source : RationalNestedSpec)
    (hr : InputRefinesSpec input source) (K : ℕ) : CDFClose (sampleLaw input hC hAd K) source.real.law (5/(2*(2:ℝ)^K)) := by
  rw [sampleLaw_eq input hC hAd source hr]
  exact source.sampleLaw_CDF_error K

end Blotto.NativeBinaryNestedSampler
