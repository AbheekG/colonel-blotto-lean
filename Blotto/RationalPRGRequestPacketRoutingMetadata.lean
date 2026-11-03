import Blotto.RationalPRGSharedPacketRoutingMetadata

/-! Cached packet/router metadata follows binary request acceptance. Incoming
input-word and field-count bounds supply one frame envelope. Packing scans and
physical array/backend/ownership/space contracts remain separate. -/

namespace Blotto.RationalPRGBinaryRequest

noncomputable def packetRoutingMetadataWork (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (frame seed : List Bool) : ℕ :=
  match readWords frame with
  | none => 0
  | some parsed => if parsed.2.2 = [] then
      let K := parsed.2.1.precision
      match seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 K) seed with
      | none => 0
      | some table => parsed.1.2.selectedPacketRoutingMetadataWork primitive c rich K table.read
    else 0

def packetRoutingMetadataFrameBound (c length : ℕ) : ℕ :=
  RationalTerminalLotto.packetRoutingMetadataBound c length (3 + (length + 2) * (4 * length + 13))

theorem packetRoutingMetadataWork_bound (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (rich : Bool) (frame seed : List Bool) :
    packetRoutingMetadataWork primitive c rich frame seed ≤ packetRoutingMetadataFrameBound c frame.length := by
  unfold packetRoutingMetadataWork
  cases hParsed : readWords frame with
  | none => exact Nat.zero_le _
  | some parsed =>
    rcases parsed with ⟨input, words, suffix⟩
    have hInput := readWords_inputWordWidth frame input words suffix hParsed
    have hSize := readWords_bounds frame input words suffix hParsed
    have hFields := Nat.add_le_add_left (RationalTerminalPacking.routingMetadataBound_mono_fields c
      (3 + (frame.length + 2) * (4 * frame.length + 13)) hSize.1)
      (RationalTerminalLotto.groupPacketMetadataBound c (3 + (frame.length + 2) * (4 * frame.length + 13)))
    dsimp only
    split
    · cases hSeed : seedTable (RationalLottoResourceSystem.sampleBitBudget input.1 words.precision) seed with
      | none => exact Nat.zero_le _
      | some table =>
        exact (input.2.selectedPacketRoutingMetadataWork_bound_of_inputWidth primitive c hPrimitive _
          (Nat.add_le_add_left hInput 3) rich words.precision table.read).trans hFields
    · exact Nat.zero_le _

noncomputable def executionWithPacketRoutingMetadataWork (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (copyResources rich : Bool) (frame seed : List Bool) : ℕ :=
  executionWithEntryConstructionMetadataWork model primitive c copyResources rich frame seed + packetRoutingMetadataWork primitive c rich frame seed

theorem executionWithPacketRoutingMetadataWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources rich : Bool) (frame seed : List Bool) :
    executionWithPacketRoutingMetadataWork model primitive c copyResources rich frame seed ≤
      executionFrameBound model c copyResources frame.length seed.length + gameMetadataBound c frame.length +
        decoderMetadataBound c frame.length + outputMetadataFrameBound c frame.length +
          9072 * dyadicMidpointMetadataBound c (frame.length + 6) + positionReaderFrameBound c frame.length +
            scalarReaderFrameBound c frame.length + constructionMetadataFrameBound c frame.length +
              entryConstructionMetadataFrameBound c frame.length + packetRoutingMetadataFrameBound c frame.length :=
  Nat.add_le_add (executionWithEntryConstructionMetadataWork_bound model primitive c hPrimitive copyResources rich frame seed)
    (packetRoutingMetadataWork_bound primitive c hPrimitive rich frame seed)

theorem packetRoutingMetadataWork_run_failure (primitive : ℕ → ℕ) (c : ℕ) (rich : Bool) (frame seed : List Bool)
    (h : run rich frame seed = none) : packetRoutingMetadataWork primitive c rich frame seed = 0 := by
  unfold run at h
  unfold packetRoutingMetadataWork
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
