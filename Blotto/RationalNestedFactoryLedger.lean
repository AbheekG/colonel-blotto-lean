import Blotto.RationalNestedFactoryWork
import Blotto.RationalNestedCombinedLedger

/-! Actual local callback components and repeated profile factories add on
the same indexed path. The constructor/data initialization is outside that
observer. Weight-list setup, output, metadata/backend/ownership remain separate. -/

namespace Blotto.RationalNestedResourceSystem

noncomputable def localDataCallbackAndFactoryBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localSourceAndTerminalBitWork model copyResources K outerBits scalarBits N bits pos hpos +
    i.terminalProfileFactoryBitWork model primitive K outerBits scalarBits N bits pos hpos

theorem localDataCallbackAndFactoryBitWork_singlePath (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localDataCallbackAndFactoryBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos =
      rationalInitialDataBitCost model i.capacity i.initial +
        (i.machine K outerBits scalarBits).cachedCallbackWork
          (fun cursor => i.localCallbackBitCharge model copyResources K outerBits cursor +
            WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
              (i.terminalProfileFactoryPrice model primitive K outerBits) cursor)
          N bits (.state i.samplingStart) pos hpos := by
  unfold localDataCallbackAndFactoryBitWork terminalProfileFactoryBitWork
  rw [localSourceAndTerminalBitWork_singlePath, WordStateMachine.cachedCallbackWork_add]
  omega

theorem FieldsHeight.localDataCallbackAndFactoryBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localDataCallbackAndFactoryBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget s 7 + 31) +
        2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) +
          19 * (3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s)) := by
  have hd := h.localSourceAndTerminalBitWork_bound hs model copyResources K hPrecision outerBits scalarBits N bits pos hpos
  have hf := h.terminalProfileFactoryBitWork_bound hs model primitive c hPrimitive K hPrecision outerBits scalarBits N bits pos hpos
  unfold localDataCallbackAndFactoryBitWork
  omega

end Blotto.RationalNestedResourceSystem
namespace Blotto.RationalFourInput

noncomputable def reflectedLocalDataCallbackAndFactoryBitWork (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let system := i.reflectedResourceSystem hcase
  rationalInitialDataBitCost model system.capacity system.initial +
    (i.reflectedMachine hcase K outerBits scalarBits).cachedCallbackWork
      (fun cursor => system.localCallbackBitCharge model copyResources K outerBits cursor +
        WordStateMachine.serialFactoryCharge system.phase (system.continuationStart K outerBits)
          (system.terminalProfileFactoryPrice model primitive K outerBits) cursor)
      N bits (.state system.samplingStart) pos hpos

theorem reflectedLocalDataCallbackAndFactoryBitWork_refines (i : RationalFourInput)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedLocalDataCallbackAndFactoryBitWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos =
      (i.reflectedResourceSystem hcase).localDataCallbackAndFactoryBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos := by
  rw [RationalNestedResourceSystem.localDataCallbackAndFactoryBitWork_singlePath]
  unfold reflectedLocalDataCallbackAndFactoryBitWork reflectedMachine
  dsimp only
  rw [WordStateMachine.cachedCallbackWork_mapped]

theorem FieldsHeight.reflectedLocalDataCallbackAndFactoryBitWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.reflectedLocalDataCallbackAndFactoryBitWork hcase model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget (max s (K + 2)) 21 + 31) +
        2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget (max s (K + 2)) 68)) +
          19 * (3 * RationalNestedInput.preparationNumericBitWork c K +
            26000 * model.rat (1 + 2 * expressionHeightBudget (max s (K + 2)) 68)) := by
  let w := max s (K + 2)
  have hw := hs.trans (le_max_left s (K + 2))
  have hSystem := (h.mono (le_max_left s (K + 2))).reflectedResourceSystem hw hcase
  have hp := hSystem.localDataCallbackAndFactoryBitWork_bound
    (hw.trans (expressionHeightBudget_ge_input w 14)) model primitive c hPrimitive copyResources K
    ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 14)) outerBits scalarBits N bits pos hpos
  rw [reflectedLocalDataCallbackAndFactoryBitWork_refines]
  unfold RationalNestedResourceSystem.terminalFactoryWidth at hp
  simp only [expressionHeightBudget_comp] at hp
  exact hp

end Blotto.RationalFourInput
