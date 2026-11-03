import Blotto.RationalPRGDispatchWork
import Blotto.RationalPRGRequestPreparationWork
import Blotto.RationalPRGRequestInputWords

/-! Preparation and selected sampler/output prices compose on the primary
request branches. Parse/suffix/seed failures charge no sampling work. The
request-dependent bound preserves both players and store interpretations;
remaining metadata/backend/physical ownership/space are not certified here. -/

namespace Blotto.RationalPRGBinaryRequest

noncomputable def samplingBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources rich : Bool)
    (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed =>
    if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.dispatchBitWork model primitive copyResources rich K table.read
    else 0

def samplingBound (model : RationalCostModel) (c : ℕ) (copyResources : Bool) (frame : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => parsed.1.2.dispatchBound model c copyResources parsed.2.1.precision

theorem samplingBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    samplingBitWork model primitive copyResources rich frame seed ≤ samplingBound model c copyResources frame := by
  unfold samplingBitWork samplingBound
  cases hParsed : readWords frame with
  | none => rfl
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact input.2.dispatchBitWork_bound model primitive c hPrimitive copyResources rich words.precision table.read
    · exact Nat.zero_le _

noncomputable def executionBitWork (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources rich : Bool)
    (frame seed : List Bool) : ℕ :=
  preparationBitWork model primitive frame seed + samplingBitWork model primitive copyResources rich frame seed

theorem executionBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionBitWork model primitive copyResources rich frame seed ≤ readPrecisionBound model c frame.length +
      seedPreparationBound c frame.length seed.length + samplingBound model c copyResources frame :=
  Nat.add_le_add (preparationBitWork_bound model primitive c hPrimitive frame seed)
    (samplingBitWork_bound model primitive c hPrimitive copyResources rich frame seed)

theorem samplingBitWork_read_failure (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources rich : Bool)
    (frame seed : List Bool) (h : readWords frame = none) : samplingBitWork model primitive copyResources rich frame seed = 0 := by
  simp only [samplingBitWork, h]

theorem samplingBitWork_suffix_failure (model : RationalCostModel) (primitive : ℕ → ℕ) (copyResources rich : Bool)
    (frame seed : List Bool) (input : Σ n, RationalPRGOriginalInput n) (words : BinaryAccuracyWords) (suffix : List Bool)
    (h : readWords frame = some (input, words, suffix)) (hSuffix : suffix ≠ []) :
    samplingBitWork model primitive copyResources rich frame seed = 0 := by
  simp only [samplingBitWork, h, ite_eq_right hSuffix]

end Blotto.RationalPRGBinaryRequest
