import Blotto.RationalPRGSharedEntryConstructionMetadata
import Blotto.RationalPRGRequestConstructionMetadataWork

/-! Parent-entry metadata follows the actual request acceptance and player
selection. A larger proved input height supplies the bound directly; no
monotonicity assumption is imposed on the natural primitive price function. -/

namespace Blotto.RationalPRGOriginalInput

theorem selectedEntryConstructionMetadataWork_bound_of_inputWidth {n : ℕ} (i : RationalPRGOriginalInput n)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (s : ℕ) (hInput : 3 + i.originalInputWordWidth ≤ s) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.selectedEntryConstructionMetadataWork primitive c rich K bits ≤ RationalTerminalLotto.entryConstructionMetadataBound c s := by
  have hs : 2 ≤ s := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ s :=
    i.normalized_lattice_wordWidth_original.trans ((show 1 + i.originalInputWordWidth ≤ 3 + i.originalInputWordWidth by omega).trans hInput)
  have hOne : RationalHeight (1 : ℚ) s :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  cases rich with
  | false =>
    exact i.normalizedInput.poorNativeSystem_on_lattice.sharedEntryConstructionMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le s hs (i.normalized_budget_height.mono hInput) hWidth
      primitive c hPrimitive _ _
  | true =>
    exact i.normalizedInput.richNativeSystem_on_lattice.sharedEntryConstructionMetadataWork_bound
      i.normalizedInput.latticeDenominator_pos le_rfl s hs hOne hWidth primitive c hPrimitive _ _

end Blotto.RationalPRGOriginalInput

namespace Blotto.RationalPRGBinaryRequest

noncomputable def entryConstructionMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedEntryConstructionMetadataWork primitive c rich K table.read
    else 0

def entryConstructionMetadataFrameBound (c length : ℕ) : ℕ :=
  RationalTerminalLotto.entryConstructionMetadataBound c (3 + (length + 2) * (4 * length + 13))

theorem entryConstructionMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    entryConstructionMetadataWork primitive c rich frame seed ≤ entryConstructionMetadataFrameBound c frame.length := by
  unfold entryConstructionMetadataWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table =>
        exact input.2.selectedEntryConstructionMetadataWork_bound_of_inputWidth primitive c hPrimitive _
          (Nat.add_le_add_left hInput 3) rich words.precision table.read
    · exact Nat.zero_le _

noncomputable def executionWithEntryConstructionMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithConstructionMetadataWork model primitive c copyResources rich frame seed + entryConstructionMetadataWork primitive c rich frame seed

theorem executionWithEntryConstructionMetadataWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithEntryConstructionMetadataWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length +
              entryConstructionMetadataFrameBound c frame.length :=
  Nat.add_le_add (executionWithConstructionMetadataWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (entryConstructionMetadataWork_bound primitive c hPrimitive rich frame seed)

theorem entryConstructionMetadataWork_run_failure (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : entryConstructionMetadataWork primitive c rich frame seed = 0 := by
  unfold run at h
  unfold entryConstructionMetadataWork
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
