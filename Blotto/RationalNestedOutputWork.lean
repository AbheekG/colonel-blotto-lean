import Blotto.CachedSerialEmissionBound
import Blotto.RationalSegmentDecodedEmission
import Blotto.RationalNestedStartDataWork
import Blotto.CachedDoneOnlyFailure

/-! The selected local categorical slot pays scalar decoding/interpolation
once. Its charge is zero on ask transitions. The one-time bound uses reached
profile heights, keeps the original cap/position, and excludes later output
maps, fallback, metadata/backend/ownership. -/

namespace Blotto.RationalNestedResourceSystem

def terminalOutputWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 57

def terminalDecodedEmissionCharge (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (state : CategoricalState (Fin 18)) : ℕ :=
  (categoricalMachine (0 : Fin 18)).emissionCharge
    (((i.terminalData value).profile K outerBits).decodedInterpolationBitCost model primitive K scalarBits) state

theorem FieldsHeight.terminalDecodedInterpolationPrice_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) (slot : Fin 18) :
    ((i.terminalData value).profile K outerBits).decodedInterpolationBitCost model primitive K scalarBits slot ≤
      RationalNestedInput.preparationNumericBitWork c K + 50 * model.rat (terminalOutputWidth s) := by
  have hProfile := (h.terminalData value hValue).profile (hs.trans (expressionHeightBudget_ge_input s 7)) K outerBits
  rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 7)), expressionHeightBudget_comp] at hProfile
  have hp := hProfile.decodedInterpolationBitCost_bound (hs.trans (expressionHeightBudget_ge_input s 54))
    model primitive c hPrimitive K scalarBits slot
  rw [max_eq_left (hPrecision.trans (expressionHeightBudget_ge_input s 54)), expressionHeightBudget_comp] at hp
  have hk : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ model.rat (terminalOutputWidth s) :=
    model.heightPrice_mono hPrecision (by decide : 3 ≤ 57)
  change ((i.terminalData value).profile K outerBits).decodedInterpolationBitCost model primitive K scalarBits slot ≤
    RationalNestedInput.preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
      39 * model.rat (terminalOutputWidth s) at hp
  omega

theorem FieldsHeight.terminalDecodedEmissionCharge_post {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (value : i.PhaseResult)
    (hValue : value.1.resource.HeightAt (expressionHeightBudget s 7)) (state : CategoricalState (Fin 18)) :
    match (i.continuationMachine K outerBits scalarBits value).step state with
    | .done _ => i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits value state ≤
        RationalNestedInput.preparationNumericBitWork c K + 50 * model.rat (terminalOutputWidth s)
    | .ask _ _ _ _ _ _ => i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits value state = 0 := by
  unfold continuationMachine RationalSegmentLottery.machine WordStateMachine.mapped
  dsimp only
  cases ht : (categoricalMachine (0 : Fin 18)).step state with
  | done slot =>
    simpa only [terminalDecodedEmissionCharge, WordStateMachine.emissionCharge, ht, WordTransition.mapValue] using
      h.terminalDecodedInterpolationPrice_bound hs model primitive c hPrimitive K hPrecision outerBits scalarBits value hValue slot
  | ask a b hb hab upper lower =>
    simp only [terminalDecodedEmissionCharge, WordStateMachine.emissionCharge, ht, WordTransition.mapValue]

def terminalDecodedEmissionBitWork (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork
    (WordStateMachine.serialHandoffCharge i.phase (i.continuationStart K outerBits) (fun _ => 0)
      (i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits))
    N bits (.state i.samplingStart) pos hpos

theorem FieldsHeight.terminalDecodedEmissionBitWork_bound {i : RationalNestedResourceSystem} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalDecodedEmissionBitWork model primitive K outerBits scalarBits N bits pos hpos ≤
      RationalNestedInput.preparationNumericBitWork c K + 50 * model.rat (terminalOutputWidth s) := by
  unfold terminalDecodedEmissionBitWork machine samplingStart
  exact i.phase.cachedSerialEmissionWork_bound_under (i.continuationMachine K outerBits scalarBits)
    (i.continuationStart K outerBits) 17 (i.continuation_rank K outerBits scalarBits)
    (i.LocalHeightInvariant 2 (expressionHeightBudget s 1))
    (fun value => value.1.resource.HeightAt (expressionHeightBudget s 7)) (h.localHeight_closed hs)
    (i.terminalDecodedEmissionCharge model primitive K outerBits scalarBits)
    (RationalNestedInput.preparationNumericBitWork c K + 50 * model.rat (terminalOutputWidth s))
    (fun value hValue state => by
      have hp := h.terminalDecodedEmissionCharge_post hs model primitive c hPrimitive K hPrecision
        outerBits scalarBits value hValue state
      cases ht : (i.continuationMachine K outerBits scalarBits value).step state with
      | done output => rw [ht] at hp; exact hp
      | ask a b hb hab upper lower => rw [ht] at hp; exact hp)
    N bits i.start h.localHeight_start pos hpos

def terminalOutputCount (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedEmissionWork (fun _ => 1) N bits (.state i.samplingStart) pos hpos

theorem terminalOutputCount_bound (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.terminalOutputCount K outerBits scalarBits N bits pos hpos ≤ 1 := by
  apply (i.machine K outerBits scalarBits).cachedEmissionWork_bound_under (fun _ => True) _ _ _ N bits i.samplingStart trivial pos hpos
  intro state _
  cases (i.machine K outerBits scalarBits).step state <;>
    simp only [WordTransition.Postcondition, le_refl, and_self]

theorem terminalOutputCount_of_none (i : RationalNestedResourceSystem) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : ((i.machine K outerBits scalarBits).runCachedIndexed N bits (.state i.samplingStart) pos hpos).1 = none) :
    i.terminalOutputCount K outerBits scalarBits N bits pos hpos = 0 :=
  (i.machine K outerBits scalarBits).cachedEmissionWork_of_none (fun _ => 1) N bits (.state i.samplingStart) pos hpos hNone

theorem terminalDecodedEmissionBitWork_of_none (i : RationalNestedResourceSystem) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N)
    (hNone : ((i.machine K outerBits scalarBits).runCachedIndexed N bits (.state i.samplingStart) pos hpos).1 = none) :
    i.terminalDecodedEmissionBitWork model primitive K outerBits scalarBits N bits pos hpos = 0 := by
  apply (i.machine K outerBits scalarBits).cachedCallbackWork_doneOnly_failure _ _ N bits (.state i.samplingStart) pos hpos hNone
  intro cursor
  cases cursor with
  | source state =>
    unfold machine WordStateMachine.serial serialTransition
    dsimp only
    cases hs : i.phase.step state with
    | done value =>
      unfold continuationMachine RationalSegmentLottery.machine WordStateMachine.mapped
      dsimp only
      cases ht : (categoricalMachine (0 : Fin 18)).step (i.continuationStart K outerBits value) with
      | done slot => trivial
      | ask a b hb hab upper lower =>
        simp only [WordTransition.mapValue, WordTransition.mapState, WordStateMachine.serialHandoffCharge,
          hs, terminalDecodedEmissionCharge, WordStateMachine.emissionCharge, ht, Nat.zero_add]
    | ask a b hb hab upper lower => simp only [WordStateMachine.serialHandoffCharge, hs]
  | continuation value state =>
    unfold machine WordStateMachine.serial serialTransition continuationMachine RationalSegmentLottery.machine WordStateMachine.mapped
    dsimp only
    cases ht : (categoricalMachine (0 : Fin 18)).step state with
    | done slot => trivial
    | ask a b hb hab upper lower =>
      simp only [WordTransition.mapValue, WordTransition.mapState, WordStateMachine.serialHandoffCharge,
        terminalDecodedEmissionCharge, WordStateMachine.emissionCharge, ht]

end Blotto.RationalNestedResourceSystem
