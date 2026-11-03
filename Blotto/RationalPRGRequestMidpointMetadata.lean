import Blotto.RationalPRGSharedMidpointMetadata
import Blotto.RationalPRGRequestOutputMetadata

/-! Global midpoint metadata is selected on the same normalized-player,
request/suffix/seed branches as primary execution. Precision monotonicity gives
an incoming-length bound; rejected requests pay no sampler midpoint metadata. -/

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedMidpointMetadataBitWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (rich : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperMidpointMetadataBitWork primitive K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperMidpointMetadataBitWork primitive K bits

theorem selectedMidpointMetadataBitWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedMidpointMetadataBitWork primitive rich K bits ≤ 9072 * dyadicMidpointMetadataBound c K := by
  have h := i.normalizedInput.sharedPaperMidpointMetadataBitWork_bounds primitive c hPrimitive K bits
  cases rich with
  | false => exact h.2
  | true => exact h.1

end Blotto.RationalPRGOriginalInput
namespace Blotto.RationalPRGBinaryRequest

noncomputable def midpointMetadataBitWork (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedMidpointMetadataBitWork primitive rich K table.read
    else 0

theorem midpointMetadataBitWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    midpointMetadataBitWork primitive rich frame seed ≤ 9072 * dyadicMidpointMetadataBound c (frame.length + 6) := by
  unfold midpointMetadataBitWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSize := readWords_bounds frame input words suffix hParsed
    have hPrice := Nat.mul_le_mul_left 9072 (dyadicMidpointMetadataBound_mono c hSize.2.2)
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact (input.2.selectedMidpointMetadataBitWork_bound primitive c hPrimitive rich words.precision table.read).trans hPrice
    · exact Nat.zero_le _

noncomputable def executionWithMidpointMetadataBitWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithOutputMetadataBitWork model primitive copyResources rich frame seed + midpointMetadataBitWork primitive rich frame seed

theorem executionWithMidpointMetadataBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithMidpointMetadataBitWork model primitive copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) :=
  Nat.add_le_add (executionWithOutputMetadataBitWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (midpointMetadataBitWork_bound primitive c hPrimitive rich frame seed)

theorem midpointMetadataBitWork_run_failure (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : midpointMetadataBitWork primitive rich frame seed = 0 := by
  unfold run at h
  unfold midpointMetadataBitWork
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
