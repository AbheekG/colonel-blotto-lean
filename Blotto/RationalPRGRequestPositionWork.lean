import Blotto.RationalPRGPositionReaderWork
import Blotto.RationalPRGRequestMidpointMetadata

/-! The actual primary visit allowance propagates through selected normalized
players and request gates. Its per-visit price covers position/cap arithmetic
and duplicated coin-reader accesses. Scalar-block invocation frequency,
descriptor/environment, physical address/backend/space remain separate. -/

namespace Blotto.RationalPRGOriginalInput

def selectedPositionReaderAllowance {n : ℕ} (i : RationalPRGOriginalInput n) (c : ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  if rich then i.normalizedInput.richNativeSystem.paperPositionReaderAllowance c K bits
  else i.normalizedInput.poorNativeSystem.paperPositionReaderAllowance c K bits

theorem selectedPositionReaderAllowance_bound {n : ℕ} (i : RationalPRGOriginalInput n) (c : ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedPositionReaderAllowance c rich K bits ≤ (10 * n + 6 * K + 6166) *
      positionReaderUnitBound c (RationalLottoResourceSystem.sampleBitBudget n K) := by
  have h := i.normalizedInput.paperPositionReaderAllowance_bounds c K bits
  cases rich with
  | false => exact h.2
  | true => exact h.1

end Blotto.RationalPRGOriginalInput
namespace Blotto.RationalPRGBinaryRequest

def positionReaderAllowance (c : ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedPositionReaderAllowance c rich K table.read
    else 0

def positionReaderFrameBound (c length : ℕ) : ℕ :=
  (16 * length + 6202) * positionReaderUnitBound c (8 * length + 3030)

theorem positionReaderAllowance_bound (c : ℕ) (rich : Bool) (frame seed : List Bool) :
    positionReaderAllowance c rich frame seed ≤ positionReaderFrameBound c frame.length := by
  unfold positionReaderAllowance
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSize := readWords_bounds frame input words suffix hParsed
    have hSeedCount := accepted_seed_budget_bound frame input words suffix hParsed
    have hPrice := Nat.mul_le_mul (show 10 * input.1 + 6 * words.precision + 6166 ≤ 16 * frame.length + 6202 by omega)
      (positionReaderUnitBound_mono c hSeedCount)
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact (input.2.selectedPositionReaderAllowance_bound c rich words.precision table.read).trans hPrice
    · exact Nat.zero_le _

noncomputable def executionWithPositionReaderAllowance (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithMidpointMetadataBitWork model primitive copyResources rich frame seed + positionReaderAllowance c rich frame seed

theorem executionWithPositionReaderAllowance_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithPositionReaderAllowance model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length :=
  Nat.add_le_add (executionWithMidpointMetadataBitWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (positionReaderAllowance_bound c rich frame seed)

theorem positionReaderAllowance_run_failure (c : ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : positionReaderAllowance c rich frame seed = 0 := by
  unfold run at h
  unfold positionReaderAllowance
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
