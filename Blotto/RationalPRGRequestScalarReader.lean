import Blotto.RationalPRGScalarUseWork
import Blotto.RationalPRGRequestPositionWork

/-! Complete outer/scalar block reader prices include factory/producer
multiplicity and the primary request gates. Actual natural argument prices
are bounded by the supplied linear envelope, with no monotonicity/CSE claim.
Descriptor/environment and physical backend/address/space remain separate. -/

namespace Blotto.RationalPRGOriginalInput

noncomputable def selectedScalarReaderWork {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.sharedPaperScalarReaderWork primitive K bits
  else i.normalizedInput.poorNativeSystem.sharedPaperScalarReaderWork primitive K bits

theorem selectedScalarReaderWork_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedScalarReaderWork primitive rich K bits ≤
      9072 * (K * RationalPRGInput.scalarReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K)) := by
  have h := i.normalizedInput.sharedPaperScalarReaderWork_bounds primitive c hPrimitive K bits
  cases rich with
  | false => exact h.2
  | true => exact h.1

end Blotto.RationalPRGOriginalInput
namespace Blotto.RationalPRGBinaryRequest

noncomputable def scalarReaderWork (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedScalarReaderWork primitive rich K table.read
    else 0

def scalarReaderFrameBound (c length : ℕ) : ℕ :=
  9072 * ((length + 6) * RationalPRGInput.scalarReaderUnitBound c (8 * length + 3030))

theorem scalarReaderWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (rich : Bool) (frame seed : List Bool) : scalarReaderWork primitive rich frame seed ≤ scalarReaderFrameBound c frame.length := by
  unfold scalarReaderWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSize := readWords_bounds frame input words suffix hParsed
    have hSeedCount := accepted_seed_budget_bound frame input words suffix hParsed
    have hPrice := Nat.mul_le_mul_left 9072
      (Nat.mul_le_mul hSize.2.2 (RationalPRGInput.scalarReaderUnitBound_mono c hSeedCount))
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact (input.2.selectedScalarReaderWork_bound primitive c hPrimitive rich words.precision table.read).trans hPrice
    · exact Nat.zero_le _

noncomputable def executionWithScalarReaderWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithPositionReaderAllowance model primitive c copyResources rich frame seed + scalarReaderWork primitive rich frame seed

theorem executionWithScalarReaderWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithScalarReaderWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length :=
  Nat.add_le_add (executionWithPositionReaderAllowance_bound model primitive c hPrimitive copyResources rich frame seed)
    (scalarReaderWork_bound primitive c hPrimitive rich frame seed)

theorem scalarReaderWork_run_failure (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : scalarReaderWork primitive rich frame seed = 0 := by
  unfold run at h
  unfold scalarReaderWork
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
