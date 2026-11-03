import Blotto.CachedSerialReachedCharges
import Blotto.RationalNestedDataOutputLedger
import Blotto.RationalNestedCallbackInvariant

/-! Every reached local callback has a full data/primitive charge envelope.
This carries source/terminal invariants rather than clipping arbitrary states.
It is used to join local work under an enclosing binary controller. -/

namespace Blotto.RationalNestedResourceSystem

theorem FieldsHeight.terminalDecodedEmissionCharge_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) (state : CategoricalState (Fin 18)) :
    i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits value state ≤
      RationalNestedInput.preparationNumericBitWork c K + 50 * model.rat (terminalOutputWidth s) := by
  unfold terminalDecodedEmissionCharge WordStateMachine.emissionCharge
  cases ht : (categoricalMachine (0 : Fin 18)).step state with
  | done slot => exact h.terminalDecodedInterpolationPrice_bound hs model primitive c hPrimitive K hPrecision outerBits scalarBits value hValue slot
  | ask a b hb hab upper lower => exact Nat.zero_le _

theorem FieldsHeight.localDataOutputCharge_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (cursor : i.SamplingState) (hCursor : i.LocalCallbackInvariant s cursor) :
    i.localDataOutputCharge model primitive copyResources K outerBits scalarBits cursor ≤
      7 * RationalNestedInput.preparationNumericBitWork c K + 52500 * model.rat (localDataOutputWidth s) := by
  let I := i.LocalStoreInvariant 2 (expressionHeightBudget s 1)
  let P := fun value : i.PhaseResult => value.1.resource.HeightAt (expressionHeightBudget s 7)
  let J := fun (_ : i.PhaseResult) (state : CategoricalState (Fin 18)) => state.Bounded 18 (expressionHeightBudget s 54)
  let price := model.rat (localDataOutputWidth s)
  have hSource : ∀ state, I state → (i.phase.step state).Postcondition I P := by
    have hp := i.localStoreInvariant_closed 2 _ (hs.trans (expressionHeightBudget_ge_input s 1)) h.capacity
    simpa only [expressionHeightBudget_comp] using hp
  have hStart : ∀ value, P value → J value (i.continuationStart K outerBits value) :=
    fun value hValue => h.continuationStart_bounded hs K hPrecision outerBits value hValue
  have hC := h.localCallbackBitCharge_bound hs model copyResources K hPrecision outerBits cursor hCursor
  have hCoef : (if copyResources then 299 else 295) ≤ 299 := by cases copyResources <;> decide
  have hCallback := hC.trans (Nat.mul_le_mul_right _ hCoef)
  have hFactory := i.phase.serialFactoryCharge_bound_under (i.continuationStart K outerBits) I P J hSource
    (i.terminalProfileFactoryPrice model primitive K outerBits)
    (3 * RationalNestedInput.preparationNumericBitWork c K + 26000 * model.rat (terminalFactoryWidth s))
    (fun value hValue => h.terminalProfileFactoryPrice_bound hs model primitive c hPrimitive K hPrecision outerBits value hValue) cursor hCursor
  have hPacket := i.phase.serialFactoryCharge_bound_under (i.continuationStart K outerBits) I P J hSource
    i.terminalPacketCopyPrice (20 * model.rat (1 + 2 * expressionHeightBudget s 7))
    (fun value hValue => h.terminalPacketCopyPrice_bound model value hValue) cursor hCursor
  have hInit := i.phase.serialPreparationCharge_bound_under I P J hSource (i.terminalStartDataPrice K outerBits)
    (36 * model.rat (terminalFactoryWidth s))
    (fun value hValue => h.terminalStartDataPrice_bound hs model K hPrecision outerBits value hValue) cursor hCursor
  have hEmit := i.phase.serialHandoffCharge_bound_under (i.continuationStart K outerBits) I P J hSource hStart
    (fun _ => 0) (i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits) 0
    (RationalNestedInput.preparationNumericBitWork c K + 50 * model.rat (terminalOutputWidth s))
    (fun _ _ => le_refl 0)
    (fun value hValue state _ => h.terminalDecodedEmissionCharge_bound hs model primitive c hPrimitive K hPrecision outerBits scalarBits value hValue state)
    cursor hCursor
  have widths := localDataOutputWidth_components s
  have hCat : model.rat (categoricalRequestWidth 18 (expressionHeightBudget s 54)) ≤ price := model.monotone widths.2.1
  have hF : model.rat (terminalFactoryWidth s) ≤ price := model.monotone widths.2.2.1
  have hP : model.rat (1 + 2 * expressionHeightBudget s 7) ≤ price := model.monotone widths.2.2.2.1
  have hO : model.rat (terminalOutputWidth s) ≤ price := model.monotone widths.2.2.2.2
  change i.localDataOutputCharge model primitive copyResources K outerBits scalarBits cursor ≤
    7 * RationalNestedInput.preparationNumericBitWork c K + 52500 * price
  unfold localDataOutputCharge
  simp only [Nat.zero_add] at hEmit
  nlinarith

end Blotto.RationalNestedResourceSystem
