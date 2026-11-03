import Blotto.BinaryThreeResourcePair
import Blotto.BinaryNestedParameters
import Blotto.RationalNestedResourcePhase

/-! Actual Boolean terminal preparation computes fractional focus, endpoint
choices, the focused rational weight and the original coordinate permutation.
It emits the six original NestedSpec fields before the separate order/mixture
controller. Rational terminal data are proof specifications, never runtime
encoders or supplied descriptor factories. -/

namespace Blotto.BinaryNestedTerminalInput
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup

abbrev State := BinaryThreeResourceState.State

def DataRefines (system : System) (state : State) (source : RationalTerminalResources) : Prop :=
  value system.M = source.M ∧ (∀ j, value (system.long.read j) = source.long j) ∧
    (∀ j, value (system.short.read j) = source.short j) ∧
    (∀ j, value (state.resource.read j) = source.resource j)

def InputRefinesSpec (input : BinaryNestedParameters.Input) (source : RationalNestedSpec) : Prop :=
  value input.M = source.M ∧ value input.a = source.a ∧ value input.d = source.d ∧
    value input.c = source.c ∧ value input.t = source.t ∧ value input.q = source.q

def focus (system : System) (state : State) : Fin 3 :=
  if BinaryThreeResourceState.fractional system.capacity state.resource 0 then 0 else
    if BinaryThreeResourceState.fractional system.capacity state.resource 1 then 1 else 2

def permutation (system : System) (state : State) : Equiv.Perm (Fin 3) := Equiv.swap (focus system state) 2

def endpoint (system : System) (state : State) (j : Fin 3) : SignedWord :=
  if BinaryEuclideanGCD.nonzero (state.resource.read j).numerator = false then
    system.long.read j else system.short.read j

def weight (system : System) (state : State) (j : Fin 3) : SignedWord :=
  BinaryRationalOpcode.apply .div (state.resource.read j) (system.capacity.read j)

def prepare (system : System) (state : State) : BinaryNestedParameters.Input :=
  let selected := focus system state
  let pi := Equiv.swap selected 2
  { M := system.M
    a := endpoint system state (pi 0)
    d := endpoint system state (pi 1)
    c := system.long.read selected
    t := system.short.read selected
    q := weight system state selected }

theorem data_capacity (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hR : DataRefines system state source) (j : Fin 3) :
    value (system.capacity.read j) = source.capacity j := by
  rw [System.capacity, FixedArrayTable.read_ofFn,
    BinaryRationalOpcode.apply_value .sub _ _ (hC.2.1 j).1 (hC.2.2.1 j).1,
    hR.2.1 j, hR.2.2.1 j]
  rfl

theorem zero_numerator_iff_value (word : SignedWord) (h : BinaryRationalOpcode.Valid word) :
    BinaryEuclideanGCD.nonzero word.numerator = false ↔ value word = 0 := by
  rw [BinaryEuclideanGCD.nonzero_false_iff]
  have hd : (BinaryBigEndian.littleValue word.denominator : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt h
  unfold value
  rw [div_eq_zero_iff]
  simp only [hd, or_false]
  cases word.negative <;> simp

theorem endpoint_canonical (system : System) (state : State) (hC : system.Canonical) (j : Fin 3) :
    CanonicalWord (endpoint system state j) := by
  unfold endpoint
  split
  · exact hC.2.1 j
  · exact hC.2.2.1 j

theorem weight_canonical (system : System) (state : State) (hC : system.Canonical)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) (j : Fin 3) :
    CanonicalWord (weight system state j) :=
  opcode_canonical .div _ _ (hState j) (capacity_canonical system hC j)

theorem prepare_canonical (system : System) (state : State) (hC : system.Canonical)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) : (prepare system state).Canonical :=
  ⟨hC.1, endpoint_canonical system state hC _, endpoint_canonical system state hC _,
    hC.2.1 _, hC.2.2.1 _, weight_canonical system state hC hState _⟩

theorem fractional_refines (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hR : DataRefines system state source) (j : Fin 3) :
    BinaryThreeResourceState.fractional system.capacity state.resource j = true ↔
      0 < source.resource j ∧ source.resource j < source.capacity j := by
  rw [BinaryThreeResourceState.fractional_iff _ _ (capacity_canonical system hC) hState j,
    hR.2.2.2 j, data_capacity system state source hC hR j]

theorem focus_refines (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hR : DataRefines system state source) : focus system state = source.focus := by
  simp only [focus, RationalTerminalResources.focus,
    fractional_refines system state source hC hState hR 0,
    fractional_refines system state source hC hState hR 1]

theorem permutation_refines (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hR : DataRefines system state source) : permutation system state = source.permutation := by
  rw [permutation, RationalTerminalResources.permutation, focus_refines system state source hC hState hR]

theorem endpoint_refines (system : System) (state : State) (source : RationalTerminalResources)
    (_hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hR : DataRefines system state source) (j : Fin 3) :
    value (endpoint system state j) = source.endpoint j := by
  unfold endpoint RationalTerminalResources.endpoint
  have hz := zero_numerator_iff_value (state.resource.read j) (hState j).1
  rw [hR.2.2.2 j] at hz
  by_cases he : source.resource j = 0
  · rw [ite_eq_left (hz.mpr he), ite_eq_left he]
    exact hR.2.1 j
  · rw [ite_eq_right (fun h => he (hz.mp h)), ite_eq_right he]
    exact hR.2.2.1 j

theorem weight_refines (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hR : DataRefines system state source) (j : Fin 3) :
    value (weight system state j) = source.weight j := by
  rw [weight, BinaryRationalOpcode.apply_value .div _ _ (hState j).1 (capacity_canonical system hC j).1,
    hR.2.2.2 j, data_capacity system state source hC hR j]
  rfl

theorem prepare_refines (system : System) (state : State) (source : RationalTerminalResources)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hR : DataRefines system state source) : InputRefinesSpec (prepare system state) source.input := by
  have hf := focus_refines system state source hC hState hR
  have hp := permutation_refines system state source hC hState hR
  change value system.M = source.M ∧
    value (endpoint system state (permutation system state 0)) = source.endpoint (source.permutation 0) ∧
    value (endpoint system state (permutation system state 1)) = source.endpoint (source.permutation 1) ∧
    value (system.long.read (focus system state)) = source.long source.focus ∧
    value (system.short.read (focus system state)) = source.short source.focus ∧
    value (weight system state (focus system state)) = source.weight source.focus
  rw [endpoint_refines system state source hC hState hR,
    endpoint_refines system state source hC hState hR, weight_refines system state source hC hState hR,
    hf, hp]
  exact ⟨hR.1, rfl, rfl, hR.2.1 _, hR.2.2.1 _, rfl⟩

-- Refinement to the exact retained terminal constructor uses only the source
-- system and terminal-state certificates already supplied by resource rounding.
theorem terminal_data_refines (system : System) (state : State) (source : RationalNestedResourceSystem)
    (s : RationalActiveResources source.capacity)
    (hs : RationalResourceInvariant source.capacity (source.totalResource : ℝ) s) (ht : s.active.length ≤ 1)
    (hSystem : system.Refines source)
    (hAllocation : ∀ j, value (state.resource.read j) = s.resource.allocation j) :
    DataRefines system state (source.terminal s hs ht) :=
  ⟨hSystem.1, hSystem.2.1, hSystem.2.2.1, hAllocation⟩

theorem prepare_terminal_refines (system : System) (state : State) (source : RationalNestedResourceSystem)
    (s : RationalActiveResources source.capacity)
    (hs : RationalResourceInvariant source.capacity (source.totalResource : ℝ) s) (ht : s.active.length ≤ 1)
    (hC : system.Canonical) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hSystem : system.Refines source)
    (hAllocation : ∀ j, value (state.resource.read j) = s.resource.allocation j) :
    InputRefinesSpec (prepare system state) (source.terminal s hs ht).input :=
  prepare_refines system state _ hC hState (terminal_data_refines system state source s hs ht hSystem hAllocation)

def ordered (input : BinaryNestedParameters.Input) : Bool :=
  BinaryRationalArithmetic.lessEqual input.a input.d

theorem ordered_iff (input : BinaryNestedParameters.Input) (source : RationalNestedSpec)
    (hC : input.Canonical) (hR : InputRefinesSpec input source) :
    ordered input = true ↔ source.a ≤ source.d := by
  rw [ordered, BinaryRationalArithmetic.lessEqual_iff _ _ hC.2.1.1 hC.2.2.1.1,
    hR.2.1, hR.2.2.1]

def sortedInput (input : BinaryNestedParameters.Input) : BinaryNestedParameters.Input :=
  { input with a := BinaryRationalOpcode.apply .minimum input.a input.d
               d := BinaryRationalOpcode.apply .maximum input.a input.d }

theorem sortedInput_canonical (input : BinaryNestedParameters.Input) (hC : input.Canonical) :
    (sortedInput input).Canonical :=
  ⟨hC.1, opcode_canonical .minimum _ _ hC.2.1 hC.2.2.1,
    opcode_canonical .maximum _ _ hC.2.1 hC.2.2.1,
    hC.2.2.2.1, hC.2.2.2.2.1, hC.2.2.2.2.2⟩

theorem sortedInput_refines (input : BinaryNestedParameters.Input) (source : RationalNestedSpec)
    (hC : input.Canonical) (hR : InputRefinesSpec input source) (hq0 : 0 < source.q) (hq1 : source.q < 1) :
    (sortedInput input).Refines (source.interiorInput hq0 hq1) := by
  refine ⟨hR.1, ?_, ?_, hR.2.2.2.1, hR.2.2.2.2.1, hR.2.2.2.2.2⟩
  · change value (BinaryRationalOpcode.apply .minimum input.a input.d) = min source.a source.d
    rw [BinaryRationalOpcode.apply_value .minimum _ _ hC.2.1.1 hC.2.2.1.1, hR.2.1, hR.2.2.1]
    rfl
  · change value (BinaryRationalOpcode.apply .maximum input.a input.d) = max source.a source.d
    rw [BinaryRationalOpcode.apply_value .maximum _ _ hC.2.1.1 hC.2.2.1.1, hR.2.1, hR.2.2.1]
    rfl

def orderPermutation (input : BinaryNestedParameters.Input) : Equiv.Perm (Fin 3) :=
  if ordered input then Equiv.refl _ else Equiv.swap 0 1

theorem orderPermutation_refines (input : BinaryNestedParameters.Input) (source : RationalNestedSpec)
    (hC : input.Canonical) (hR : InputRefinesSpec input source) :
    orderPermutation input = if source.a ≤ source.d then Equiv.refl _ else Equiv.swap 0 1 := by
  simp only [orderPermutation, ordered_iff input source hC hR]

end Blotto.BinaryNestedTerminalInput
