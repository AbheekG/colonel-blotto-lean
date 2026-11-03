import Blotto.RationalPRGRequestExecutionWork
import Blotto.RationalPRGDispatchEnvelope

/-! The composed request work now has a seed-independent incoming-length
bound for both players and both resource-store interpretations. Its finite
formula retains Rat and natural primitive parameters. Remaining metadata,
backend/physical ownership/space contracts are separate. -/

namespace Blotto.RationalPRGBinaryRequest

def samplingFrameBound (model : RationalCostModel) (c : ℕ) (copyResources : Bool) (length : ℕ) : ℕ :=
  RationalPRGOriginalInput.dispatchEnvelope model c copyResources length ((length + 2) * (4 * length + 13)) (length + 6)

theorem samplingBound_frame_bound (model : RationalCostModel) (c : ℕ) (copyResources : Bool) (frame : List Bool) :
    samplingBound model c copyResources frame ≤ samplingFrameBound model c copyResources frame.length := by
  unfold samplingBound
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSizes := readWords_bounds frame input words suffix hParsed
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    dsimp only
    rw [RationalPRGOriginalInput.dispatchBound_eq_envelope]
    exact RationalPRGOriginalInput.dispatchEnvelope_mono model c copyResources hSizes.1 hInput hSizes.2.2

def executionFrameBound (model : RationalCostModel) (c : ℕ) (copyResources : Bool)
    (requestLength seedLength : ℕ) : ℕ :=
  readPrecisionBound model c requestLength + seedPreparationBound c requestLength seedLength +
    samplingFrameBound model c copyResources requestLength

theorem executionBitWork_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionBitWork model primitive copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length :=
  (executionBitWork_bound model primitive c hPrimitive copyResources rich frame seed).trans
    (Nat.add_le_add_left (samplingBound_frame_bound model c copyResources frame) _)

theorem samplingBitWork_run_failure (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources rich : Bool)
    (frame seed : List Bool) (h : run rich frame seed = none) :
    samplingBitWork model primitive copyResources rich frame seed = 0 := by
  unfold run at h
  unfold samplingBitWork
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
      | some table =>
        rw [hSeed, Option.map_some] at h
        cases h
    · rename_i hSuffix
      rw [ite_eq_right hSuffix]

end Blotto.RationalPRGBinaryRequest
