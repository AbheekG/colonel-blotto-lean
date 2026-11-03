import Blotto.RationalPRGSharedPackingCopyWork

/-! Packing metadata and full-array route payload copying follow accepted
binary requests. This conservative component permits repeated array copies;
the faster in-place contract and physical backend/space remain separate. -/

namespace Blotto.RationalPRGBinaryRequest

noncomputable def packingCopyWork (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedPackingCopyWork primitive rich K table.read
    else 0

def packingCopyFrameBound (c length : ℕ) : ℕ :=
  RationalTerminalLotto.packingCopyBound c length (3 + (length + 2) * (4 * length + 13))

theorem packingCopyWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    packingCopyWork primitive rich frame seed ≤ packingCopyFrameBound c frame.length := by
  unfold packingCopyWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    have hSize := readWords_bounds frame input words suffix hParsed
    have hFields := RationalTerminalLotto.packingCopyBound_mono_fields c
      (3 + (frame.length + 2) * (4 * frame.length + 13)) hSize.1
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table =>
        exact (input.2.selectedPackingCopyWork_bound_of_inputWidth primitive c hPrimitive _
          (Nat.add_le_add_left hInput 3) rich words.precision table.read).trans hFields
    · exact Nat.zero_le _

noncomputable def executionWithPackingCopyWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithPacketRoutingMetadataWork model primitive c copyResources rich frame seed + packingCopyWork primitive rich frame seed

theorem executionWithPackingCopyWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithPackingCopyWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length +
              entryConstructionMetadataFrameBound c frame.length + packetRoutingMetadataFrameBound c frame.length +
                packingCopyFrameBound c frame.length :=
  Nat.add_le_add (executionWithPacketRoutingMetadataWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (packingCopyWork_bound primitive c hPrimitive rich frame seed)

theorem packingCopyWork_run_failure (primitive : ℕ → ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : packingCopyWork primitive rich frame seed = 0 := by
  unfold run at h
  unfold packingCopyWork
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
