import Blotto.CachedSerialFactoryWork
import Blotto.RationalTerminalResourcePreparation
import Blotto.RationalNestedResourceCostInvariant

/-! Local serial control constructs a profile for the continuation machine
at each terminal callback and another profile for its initial categorical
state at handoff. Both are priced conservatively by the full construction
envelope. Terminal packet copies, weight-list setup and backend are separate. -/

namespace Blotto.RationalNestedResourceSystem

def terminalFactoryWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 54

noncomputable def terminalProfileFactoryPrice (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (K : ℕ) (outerBits : Fin K → Bool) (value : i.PhaseResult) : ℕ :=
  (i.terminalData value).profilePreparedBitCost model primitive K outerBits

theorem FieldsHeight.terminalProfileFactoryPrice_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) :
    i.terminalProfileFactoryPrice model primitive K outerBits value ≤
      3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s) := by
  have hFields := h.terminalData value hValue
  have hp := hFields.profilePreparedBitCost_bound (hs.trans (expressionHeightBudget_ge_input s 7))
    model primitive c hPrimitive K outerBits
  rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 7))] at hp
  rw [expressionHeightBudget_comp] at hp
  exact hp

noncomputable def terminalProfileFactoryBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
      (i.terminalProfileFactoryPrice model primitive K outerBits))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalProfileFactoryBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalProfileFactoryBitWork model primitive K outerBits scalarBits N bits pos hpos ≤
      19 * (3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s)) := by
  unfold terminalProfileFactoryBitWork machine samplingStart
  have hp := i.phase.cachedSerialFactoryWork_bound_under (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) (h.localHeight_closed hs)
    (i.terminalProfileFactoryPrice model primitive K outerBits)
    (3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s))
    (fun value hValue => h.terminalProfileFactoryPrice_bound hs model primitive c hPrimitive K hPrecision outerBits value hValue)
    N bits i.start h.localHeight_start pos hpos
  simpa only [Nat.mul_comm] using hp

def terminalProfileFactoryCount (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits) (fun _ => 1))
    N bits (.state i.samplingStart) pos hpos

theorem terminalProfileFactoryCount_bound (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalProfileFactoryCount K outerBits scalarBits N bits pos hpos ≤ 19 := by
  unfold terminalProfileFactoryCount machine samplingStart
  exact i.phase.cachedSerialFactoryCount_bound (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits) N bits i.start pos hpos

end Blotto.RationalNestedResourceSystem
