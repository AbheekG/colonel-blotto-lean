import Blotto.BinaryNestedTerminalInput
import Blotto.BinaryReflectedSetupWork
import Blotto.BinaryGeneralResourceExecution
import Blotto.BinaryReflectedReachedHeight
import Blotto.BinaryNestedParameterWork

/-! Native terminal input preparation retains one computed capacity table and
focus, returning the six original nested fields and permutation. Its primitive
capacity/guard/endpoint/division prices follow stored-word heights. Metadata,
bookkeeping, table ownership and the nested profile factory are separate. -/

namespace Blotto.BinaryNestedTerminalPreparationWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryReflectedFourSetup BinaryGeneralResourceExecution

def SystemHeight (system : System) (s : ℕ) : Prop :=
  RationalHeight (value system.M) s ∧ (∀ j, RationalHeight (value (system.long.read j)) s) ∧
    ∀ j, RationalHeight (value (system.short.read j)) s

def focusWithWork (capacity resource : FixedArrayTable 3 SignedWord) : Fin 3 × ℕ :=
  let first := fractionalWithCharge capacity resource 0
  if first.1 then (0,first.2.booleanWork) else
    let second := fractionalWithCharge capacity resource 1
    (if second.1 then 1 else 2,first.2.booleanWork + second.2.booleanWork)

theorem focusWithWork_state (system : System) (state : BinaryThreeResourceState.State) :
    (focusWithWork system.capacity state.resource).1 = BinaryNestedTerminalInput.focus system state := by
  unfold focusWithWork fractionalWithCharge BinaryNestedTerminalInput.focus BinaryThreeResourceState.fractional
  dsimp only
  split_ifs <;> rfl

theorem focusWithWork_bound (capacity resource : FixedArrayTable 3 SignedWord) (W : ℕ) (hW : 1 ≤ W)
    (hCap : ∀ j, width (capacity.read j) ≤ W) (hResource : ∀ j, width (resource.read j) ≤ W) :
    (focusWithWork capacity resource).2 ≤ 2000 * (W + 1) ^ 2 := by
  have h0 := fractionalWithCharge_bound capacity resource 0 W hW (hCap 0) (hResource 0)
  have h1 := fractionalWithCharge_bound capacity resource 1 W hW (hCap 1) (hResource 1)
  unfold focusWithWork
  dsimp only
  split <;> dsimp only <;> omega

def endpointWithWork (system : System) (state : BinaryThreeResourceState.State) (j : Fin 3) : SignedWord × ℕ :=
  (BinaryNestedTerminalInput.endpoint system state j, 2 * ((state.resource.read j).numerator.length + 1))

def prepareWithWork (system : System) (state : BinaryThreeResourceState.State) :
    (BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × ℕ :=
  let capacity := BinaryReflectedSetupWork.capacityWithWork system
  let selected := focusWithWork capacity.1 state.resource
  let pi := Equiv.swap selected.1 2
  let first := endpointWithWork system state (pi 0)
  let second := endpointWithWork system state (pi 1)
  let probability := applyWithWork .div (state.resource.read selected.1) (capacity.1.read selected.1)
  ((⟨system.M,first.1,second.1,system.long.read selected.1,system.short.read selected.1,probability.1⟩,pi),
    capacity.2 + selected.2 + first.2 + second.2 + probability.2)

theorem prepareWithWork_state (system : System) (state : BinaryThreeResourceState.State) :
    (prepareWithWork system state).1 =
      (BinaryNestedTerminalInput.prepare system state,BinaryNestedTerminalInput.permutation system state) := by
  unfold prepareWithWork
  simp only [BinaryReflectedSetupWork.capacityWithWork_state,focusWithWork_state,endpointWithWork,applyWithWork_state]
  rfl

def bound (s : ℕ) : ℕ :=
  48000 * (2 + 2 * expressionHeightBudget s 1) ^ 3 +
    2000 * (2 + 2 * expressionHeightBudget s 1) ^ 2 + 8 + 8 * s

theorem prepareWithWork_bound (system : System) (state : BinaryThreeResourceState.State)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j)) (s : ℕ)
    (hSystem : SystemHeight system s) (hResource : ∀ j, RationalHeight (value (state.resource.read j)) s) :
    (prepareWithWork system state).2 ≤ bound s := by
  let H := expressionHeightBudget s 1
  let W := 1 + 2 * H
  have hsH : s ≤ H := expressionHeightBudget_ge_input s 1
  have hCapacity := BinaryReflectedSetupWork.capacityWithWork_bound system hC s hSystem.2.1 hSystem.2.2
  have hCapHeight : ∀ j, RationalHeight (value (system.capacity.read j)) H := by
    intro j
    rw [System.capacity,FixedArrayTable.read_ofFn,apply_value .sub _ _ (hC.2.1 j).1 (hC.2.2.1 j).1]
    have hl : RationalHeight (value (system.long.read j)) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hSystem.2.1 j
    have ht : RationalHeight (value (system.short.read j)) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hSystem.2.2 j
    exact hl.sub_level ht
  have hCapW := fun j => (capacity_canonical system hC j).2.trans (rationalWordWidth_of_height (hCapHeight j))
  have hResourceW : ∀ j, width (state.resource.read j) ≤ W := fun j =>
    (hState j).2.trans ((rationalWordWidth_of_height (hResource j)).trans (by dsimp only [W]; omega))
  have hFocus := focusWithWork_bound system.capacity state.resource W (by dsimp only [W]; omega) hCapW hResourceW
  let selected := BinaryNestedTerminalInput.focus system state
  let pi := Equiv.swap selected 2
  have hDiv := BinaryPRGPreparationWork.operation_uniform_bound .div (state.resource.read selected) (system.capacity.read selected)
    W (hResourceW selected) (hCapW selected)
  have hEndpoint : ∀ j, 2 * ((state.resource.read j).numerator.length + 1) ≤ 4 + 4 * s := by
    intro j
    have hw := (hState j).2.trans (rationalWordWidth_of_height (hResource j))
    unfold width at hw
    omega
  have h0 := hEndpoint (pi 0)
  have h1 := hEndpoint (pi 1)
  unfold prepareWithWork
  simp only [BinaryReflectedSetupWork.capacityWithWork_state,focusWithWork_state,endpointWithWork]
  change (BinaryReflectedSetupWork.capacityWithWork system).2 + (focusWithWork system.capacity state.resource).2 +
    2 * ((state.resource.read (pi 0)).numerator.length + 1) + 2 * ((state.resource.read (pi 1)).numerator.length + 1) +
    (applyWithWork .div (state.resource.read selected) (system.capacity.read selected)).2 ≤ _
  have hMon := Nat.pow_le_pow_left (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hsH) 2) 3
  unfold bound
  dsimp only [H,W] at hFocus hDiv hMon
  nlinarith

theorem input_height_of_refines (input : BinaryNestedParameters.Input) (source : RationalNestedSpec)
    (hR : BinaryNestedTerminalInput.InputRefinesSpec input source) (s : ℕ) (hH : source.FieldsHeight s) :
    BinaryNestedParameterWork.InputHeight input s := by
  unfold BinaryNestedParameterWork.InputHeight
  rw [hR.1,hR.2.1,hR.2.2.1,hR.2.2.2.1,hR.2.2.2.2.1,hR.2.2.2.2.2]
  exact hH

theorem reached_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) :
    (prepareWithWork (BinaryReflectedFourSetup.prepare input) result.state).2 ≤ bound (expressionHeightBudget s 21) := by
  have hSystem := prepare_refines input source hC hR hCase
  have hHeight := hH.reflectedResourceSystem hs hCase
  have hMono := expressionHeightBudget_mono s (by decide : 14 ≤ 21)
  apply prepareWithWork_bound _ _ (prepare_canonical input hC) result.canonical
  · refine ⟨?_,?_,?_⟩
    · rw [hSystem.1]; exact hHeight.1.mono hMono
    · intro j; rw [hSystem.2.1 j]; exact (hHeight.2.1 j).mono hMono
    · intro j; rw [hSystem.2.2.1 j]; exact (hHeight.2.2.1 j).mono hMono
  · exact BinaryReflectedReachedHeight.reached_resource_height input source hC hR hCase s hs hH N bits result hSuccess

theorem reached_input_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (BinaryReflectedFourSetup.prepare input).capacity)
    (hSuccess : (BinarySharedResourceRun.setupRun input hC N bits).1 = some result) :
    BinaryNestedParameterWork.InputHeight (prepareWithWork (BinaryReflectedFourSetup.prepare input) result.state).1.1
      (expressionHeightBudget s 23) := by
  rw [prepareWithWork_state]
  let terminal := BinaryReachedTerminal.terminal input source hC hR hCase N bits result hSuccess
  have hData := BinaryReachedTerminal.terminal_data_refines input source hC hR hCase N bits result hSuccess
  have hRef := BinaryNestedTerminalInput.prepare_refines _ _ terminal (prepare_canonical input hC) result.canonical hData
  have hTerminal := BinaryReflectedReachedHeight.terminal_height input source hC hR hCase s hs hH N bits result hSuccess
  have hInput := hTerminal.input
  rw [expressionHeightBudget_comp] at hInput
  exact input_height_of_refines _ terminal.input hRef _ hInput

end Blotto.BinaryNestedTerminalPreparationWork
