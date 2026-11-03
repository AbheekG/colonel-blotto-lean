import Blotto.RationalNestedMidpointMetadata
import Blotto.RationalNestedProcessingLedger
import Blotto.CachedEmissionWork

/-! Factory midpoint metadata and the one-time output midpoint decoding add
on the existing capped local execution. All metadata prices are independent
of selected numerical values, and output metadata is zero on exhaustion. -/

namespace Blotto.RationalNestedResourceSystem

def terminalOutputMidpointMetadataBitWork (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedEmissionWork (fun _ => dyadicMidpointMetadataBitWork primitive K scalarBits)
    N bits (.state i.samplingStart) pos hpos

theorem terminalOutputMidpointMetadataBitWork_bound (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalOutputMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos ≤ dyadicMidpointMetadataBound c K := by
  unfold terminalOutputMidpointMetadataBitWork
  rw [WordStateMachine.cachedEmissionWork_eq]
  cases h : ((i.machine K outerBits scalarBits).runCachedIndexed N bits (.state i.samplingStart) pos hpos).1 with
  | none => exact Nat.zero_le _
  | some output => exact dyadicMidpointMetadataBitWork_bound primitive c hPrimitive K scalarBits

theorem terminalOutputMidpointMetadataBitWork_failure (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : ((i.machine K outerBits scalarBits).runCachedIndexed N bits (.state i.samplingStart) pos hpos).1 = none) :
    i.terminalOutputMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos = 0 :=
  (i.machine K outerBits scalarBits).cachedEmissionWork_of_none _ N bits (.state i.samplingStart) pos hpos hNone

def localMidpointMetadataBitWork (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.terminalProfileMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos +
    i.terminalOutputMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos

theorem localMidpointMetadataBitWork_bound (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos ≤ 58 * dyadicMidpointMetadataBound c K := by
  have hFactory := i.terminalProfileMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits N bits pos hpos
  have hOutput := i.terminalOutputMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits N bits pos hpos
  unfold localMidpointMetadataBitWork
  omega

noncomputable def localProcessingWithMidpointMetadataWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localProcessingWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.localMidpointMetadataBitWork primitive K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.localProcessingWithMidpointMetadataWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localProcessingWithMidpointMetadataWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      58 * RationalNestedInput.preparationNumericBitWork c K + 498000 * model.rat (localDataOutputWidth (max s (K + 2))) +
        76 * localControlWordHeight (max s (K + 2)) +
          (24 * localControlWordHeight (max s (K + 2)) + 28) * (40 + 2 * (N - pos)) + 58 * dyadicMidpointMetadataBound c K :=
  Nat.add_le_add (h.localProcessingWork_bound hs model primitive c hPrimitive copyResources K outerBits scalarBits N bits pos hpos)
    (i.localMidpointMetadataBitWork_bound primitive c hPrimitive K outerBits scalarBits N bits pos hpos)

end Blotto.RationalNestedResourceSystem
