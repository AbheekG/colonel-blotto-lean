import Blotto.CachedSerialPreparationUnder
import Blotto.RationalNestedFactoryLedger

/-! The categorical start materializes eighteen weight-list entries once at
handoff. Rational read/write words are priced separately from profile factories;
Fin tags, list allocation, packet copies and physical ownership remain separate. -/

namespace Blotto.RationalNestedResourceSystem
open scoped BigOperators

def terminalStartDataPrice (i : RationalNestedResourceSystem) (K : ℕ) (outerBits : Fin K → Bool)
    (value : i.PhaseResult) : ℕ :=
  2 * ∑ slot : Fin 18, rationalWordWidth (((i.terminalData value).profile K outerBits).weight slot)

theorem FieldsHeight.terminalStartDataPrice_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) :
    i.terminalStartDataPrice K outerBits value ≤ 36 * model.rat (terminalFactoryWidth s) := by
  have hProfile := (h.terminalData value hValue).profile (hs.trans (expressionHeightBudget_ge_input s 7)) K outerBits
  rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 7)), expressionHeightBudget_comp] at hProfile
  have hSum : (∑ slot : Fin 18, rationalWordWidth (((i.terminalData value).profile K outerBits).weight slot)) ≤
      18 * model.rat (terminalFactoryWidth s) := by
    calc
      _ ≤ ∑ _slot : Fin 18, model.rat (terminalFactoryWidth s) := Finset.sum_le_sum (fun slot _ =>
        (rationalWordWidth_of_height (hProfile.1 slot)).trans (model.word_le _))
      _ = _ := by simp
  unfold terminalStartDataPrice
  omega

def terminalStartDataBitWork (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialPreparationCharge i.phase (i.terminalStartDataPrice K outerBits))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalStartDataBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalStartDataBitWork K outerBits scalarBits N bits pos hpos ≤ 36 * model.rat (terminalFactoryWidth s) := by
  unfold terminalStartDataBitWork machine samplingStart
  exact i.phase.cachedSerialPreparationWork_bound_under (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) (h.localHeight_closed hs)
    (i.terminalStartDataPrice K outerBits) (36 * model.rat (terminalFactoryWidth s))
    (fun value hValue => h.terminalStartDataPrice_bound hs model K hPrecision outerBits value hValue)
    N bits i.start h.localHeight_start pos hpos

noncomputable def localDataCallbackFactoryAndStartBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  i.localDataCallbackAndFactoryBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos +
    i.terminalStartDataBitWork K outerBits scalarBits N bits pos hpos

theorem localDataCallbackFactoryAndStartBitWork_singlePath (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (copyResources : Bool) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localDataCallbackFactoryAndStartBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos =
      rationalInitialDataBitCost model i.capacity i.initial + (i.machine K outerBits scalarBits).cachedCallbackWork
        (fun cursor => i.localCallbackBitCharge model copyResources K outerBits cursor +
          WordStateMachine.serialFactoryCharge i.phase (i.continuationStart K outerBits)
            (i.terminalProfileFactoryPrice model primitive K outerBits) cursor +
          WordStateMachine.serialPreparationCharge i.phase (i.terminalStartDataPrice K outerBits) cursor)
        N bits (.state i.samplingStart) pos hpos := by
  unfold localDataCallbackFactoryAndStartBitWork terminalStartDataBitWork
  rw [localDataCallbackAndFactoryBitWork_singlePath]
  simp only [WordStateMachine.cachedCallbackWork_add, Nat.add_assoc]

theorem FieldsHeight.localDataCallbackFactoryAndStartBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.localDataCallbackFactoryAndStartBitWork model primitive copyResources K outerBits scalarBits N bits pos hpos ≤
      (if copyResources then 407 else 399) * model.rat (32 * expressionHeightBudget s 7 + 31) +
        2790 * model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) +
          19 * (3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s)) +
            36 * model.rat (terminalFactoryWidth s) := by
  have hd := h.localDataCallbackAndFactoryBitWork_bound hs model primitive c hPrimitive copyResources K hPrecision
    outerBits scalarBits N bits pos hpos
  have hs' := h.terminalStartDataBitWork_bound hs model K hPrecision outerBits scalarBits N bits pos hpos
  unfold localDataCallbackFactoryAndStartBitWork
  omega

end Blotto.RationalNestedResourceSystem
