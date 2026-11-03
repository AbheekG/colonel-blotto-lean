import Blotto.RationalPRGOutputMetadataWork
import Blotto.RationalPRGDecoderMetadataWork

/-! Selected scaled-row/output framing metadata follows the primary request
gates and is bounded only by incoming request length. Rejected runs emit no
output and pay zero output metadata. Local sampler metadata and physical
backend/address/record/ownership/space contracts remain separate. -/

namespace Blotto.RationalPRGBinaryRequest

def outputMetadataBitWork (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed =>
    if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedOutputMetadataBitWork primitive rich K table.read
    else 0

def outputMetadataFrameBound (c length : ℕ) : ℕ :=
  RationalPRGOriginalInput.outputMetadataBound c length (2 ^ 77 * ((length + 2) * (4 * length + 13) + length + 12))

theorem outputMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    outputMetadataBitWork primitive rich frame seed ≤ outputMetadataFrameBound c frame.length := by
  unfold outputMetadataBitWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSize := readWords_bounds frame input words suffix hParsed
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    have hWidth : input.2.outputMetadataWidth words.precision ≤
        2 ^ 77 * ((frame.length + 2) * (4 * frame.length + 13) + frame.length + 12) :=
      Nat.mul_le_mul_left _ (by omega)
    have hBound := RationalPRGOriginalInput.outputMetadataBound_mono c hSize.1 hWidth
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact (input.2.selectedOutputMetadataBitWork_bound primitive c hPrimitive rich words.precision table.read).trans hBound
    · exact Nat.zero_le _

noncomputable def executionWithOutputMetadataBitWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithDecoderMetadataBitWork model primitive copyResources rich frame seed + outputMetadataBitWork primitive rich frame seed

theorem executionWithOutputMetadataBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithOutputMetadataBitWork model primitive copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length :=
  Nat.add_le_add (executionWithDecoderMetadataBitWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (outputMetadataBitWork_bound primitive c hPrimitive rich frame seed)

theorem outputMetadataBitWork_run_failure (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : outputMetadataBitWork primitive rich frame seed = 0 := by
  unfold run at h
  unfold outputMetadataBitWork
  cases hParsed : readWords frame with
  | none => rfl
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    rw [hParsed, Option.bind_some] at h
    dsimp only at h ⊢
    split at h
    · rename_i hSuffix
      rw [ite_eq_left hSuffix]
      cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => rfl
      | some table => rw [hSeed, Option.map_some] at h; cases h
    · rename_i hSuffix
      rw [ite_eq_right hSuffix]

end Blotto.RationalPRGBinaryRequest
