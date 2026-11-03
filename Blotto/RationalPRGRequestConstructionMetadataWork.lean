import Blotto.RationalPRGSharedConstructionMetadataWork
import Blotto.RationalPRGRequestScalarReader

/-! Runtime factory metadata follows accepted binary request/player/seed
branches. Parent entry preparation, remaining metadata and physical execution
contracts remain separate from this appended component. -/

namespace Blotto.RationalPRGBinaryRequest

noncomputable def constructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedConstructionMetadataWork primitive c rich K table.read
    else 0

def constructionMetadataFrameBound (c length : ℕ) : ℕ :=
  2592 * RationalTerminalResources.profileConstructionMetadataBound c
    (expressionHeightBudget (max (3 + (length + 2) * (4 * length + 13)) (length + 8)) 22) (length + 6)

theorem constructionMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    constructionMetadataWork primitive c rich frame seed ≤ constructionMetadataFrameBound c frame.length := by
  unfold constructionMetadataWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hSize := readWords_bounds frame input words suffix hParsed
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    have hMax : max (3 + input.2.originalInputWordWidth) (words.precision + 2) ≤
        max (3 + (frame.length + 2) * (4 * frame.length + 13)) (frame.length + 8) :=
      max_le_max (Nat.add_le_add_left hInput 3) (by omega)
    have hPrice := Nat.mul_le_mul_left 2592 (RationalTerminalResources.profileConstructionMetadataBound_mono c
      (expressionHeightBudget_input_mono hMax 22) hSize.2.2)
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table => exact (input.2.selectedConstructionMetadataWork_bound primitive c hPrimitive rich words.precision table.read).trans hPrice
    · exact Nat.zero_le _

noncomputable def executionWithConstructionMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithScalarReaderWork model primitive c copyResources rich frame seed + constructionMetadataWork primitive c rich frame seed

theorem executionWithConstructionMetadataWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithConstructionMetadataWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length :=
  Nat.add_le_add (executionWithScalarReaderWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (constructionMetadataWork_bound primitive c hPrimitive rich frame seed)

theorem constructionMetadataWork_run_failure (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : constructionMetadataWork primitive c rich frame seed = 0 := by
  unfold run at h
  unfold constructionMetadataWork
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
