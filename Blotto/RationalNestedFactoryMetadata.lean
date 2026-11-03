import Blotto.RationalTerminalConstructionMetadata
import Blotto.RationalNestedFactoryLedger

/-! The complete terminal construction metadata price follows actual serial
factory reconstruction. Source heights are transferred only for reached outputs;
handoff pays two prices and continuation callbacks one. No caching is assumed. -/

namespace Blotto.RationalNestedResourceSystem

def terminalConstructionMetadataPrice (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c K : ℕ)
    (outerBits : Fin K → Bool) (value : i.PhaseResult) : ℕ :=
  RationalTerminalResources.profileConstructionMetadataWork primitive c (i.terminalData value) K outerBits

theorem FieldsHeight.terminalConstructionMetadataPrice_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) :
    i.terminalConstructionMetadataPrice primitive c K outerBits value ≤
      RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 7) K :=
  (h.terminalData value hValue).profileConstructionMetadataWork_common
    (hs.trans (expressionHeightBudget_ge_input s 7)) primitive c hPrimitive K
    (hK.trans (expressionHeightBudget_ge_input s 7)) outerBits

def terminalConstructionMetadataWork (i : RationalNestedResourceSystem) (primitive : ℕ → ℕ) (c K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits) (i.terminalConstructionMetadataPrice primitive c K outerBits))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalConstructionMetadataWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos ≤
      19 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 7) K := by
  unfold terminalConstructionMetadataWork machine samplingStart
  have hWork := i.phase.cachedSerialFactoryWork_bound_under (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) (h.localHeight_closed hs)
    (i.terminalConstructionMetadataPrice primitive c K outerBits)
    (RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 7) K)
    (fun value hValue => h.terminalConstructionMetadataPrice_bound hs primitive c hPrimitive K hK outerBits value hValue)
    N bits i.start h.localHeight_start pos hpos
  simpa only [Nat.mul_comm] using hWork

noncomputable def localFactoryWorkWithConstructionMetadata (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localDataCallbackAndFactoryBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.terminalConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.localFactoryWorkWithConstructionMetadata_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hK : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localFactoryWorkWithConstructionMetadata model primitive c copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget s 7 + 31) +
        2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) +
          19 * (3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s)) +
            19 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 7) K :=
  Nat.add_le_add (h.localDataCallbackAndFactoryBitWork_bound hs model primitive c hPrimitive copyResources K hK outerBits scalarBits N bits pos hpos)
    (h.terminalConstructionMetadataWork_bound hs primitive c hPrimitive K hK outerBits scalarBits N bits pos hpos)

end Blotto.RationalNestedResourceSystem
