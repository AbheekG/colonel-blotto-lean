import Blotto.BinaryReflectedSetupCache

/-! Terminal input construction consumes the retained reflected capacity table
and computes focus/endpoints/probability once. Its fields and permutation equal
the original constructor; the old primitive price dominates the new suffix,
with capacity production charged only by the cached prefix. -/

namespace Blotto.BinaryReflectedCachedTerminalInput
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryReflectedFourSetup
open BinaryReflectedSetupCache

def Prepared.terminalWithWork {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (state : BinaryThreeResourceState.State) : (BinaryNestedParameters.Input × Equiv.Perm (Fin 3)) × ℕ :=
  let selected := BinaryNestedTerminalPreparationWork.focusWithWork prepared.capacity state.resource
  let pi := Equiv.swap selected.1 2
  let first := BinaryNestedTerminalPreparationWork.endpointWithWork prepared.system state (pi 0)
  let second := BinaryNestedTerminalPreparationWork.endpointWithWork prepared.system state (pi 1)
  let probability := applyWithWork .div (state.resource.read selected.1) (prepared.capacity.read selected.1)
  ((⟨prepared.system.M,first.1,second.1,prepared.system.long.read selected.1,prepared.system.short.read selected.1,probability.1⟩,pi),
    selected.2 + first.2 + second.2 + probability.2)

theorem terminalWithWork_state {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (state : BinaryThreeResourceState.State) :
    (Prepared.terminalWithWork prepared state).1 =
      (BinaryNestedTerminalInput.prepare prepared.system state,BinaryNestedTerminalInput.permutation prepared.system state) := by
  unfold Prepared.terminalWithWork
  rw [prepared.capacity_correct]
  simp only [BinaryNestedTerminalPreparationWork.focusWithWork_state,
    BinaryNestedTerminalPreparationWork.endpointWithWork,applyWithWork_state]
  rfl

theorem terminalWithWork_original {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (state : BinaryThreeResourceState.State) :
    (Prepared.terminalWithWork prepared state).1 =
      (BinaryNestedTerminalInput.prepare (prepare input) state,BinaryNestedTerminalInput.permutation (prepare input) state) := by
  rw [terminalWithWork_state,prepared.system_correct]

theorem terminalWithWork_prefix_price {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (state : BinaryThreeResourceState.State) :
    (Prepared.terminalWithWork prepared state).2 + (BinaryReflectedSetupWork.capacityWithWork prepared.system).2 =
      (BinaryNestedTerminalPreparationWork.prepareWithWork prepared.system state).2 := by
  unfold Prepared.terminalWithWork BinaryNestedTerminalPreparationWork.prepareWithWork
  simp only [prepared.capacity_correct,BinaryReflectedSetupWork.capacityWithWork_state]
  omega

theorem terminalWithWork_bound {input : BinaryFourParameters.Input} (prepared : Prepared input)
    (state : BinaryThreeResourceState.State) (hState : ∀ j, CanonicalWord (state.resource.read j)) (s : ℕ)
    (hSystem : BinaryNestedTerminalPreparationWork.SystemHeight prepared.system s)
    (hResource : ∀ j, RationalHeight (value (state.resource.read j)) s) :
    (Prepared.terminalWithWork prepared state).2 ≤ BinaryNestedTerminalPreparationWork.bound s := by
  have hPrice := BinaryNestedTerminalPreparationWork.prepareWithWork_bound prepared.system state prepared.canonical hState s hSystem hResource
  have hEq := terminalWithWork_prefix_price prepared state
  omega

end Blotto.BinaryReflectedCachedTerminalInput
