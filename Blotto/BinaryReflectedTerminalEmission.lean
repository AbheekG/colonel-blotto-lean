import Blotto.BinaryTerminalProfileCompiler
import Blotto.BinarySegmentPoint
import Blotto.RationalFourReflectedProgram

/-! A native reflected terminal emission compiles its actual nested table,
interpolates a selected slot with stored Boolean arithmetic, then subtracts from
the original three lengths and appends zero. Every slot and bit path retains
original budget and box bounds. Shared categorical selection is a separate join. -/

namespace Blotto.BinaryReflectedTerminalEmission
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinaryNestedTerminalInput

def sample (input : BinaryFourParameters.Input) (state : State) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    FixedArrayTable 4 SignedWord :=
  reflect input (BinarySegmentPoint.sample (BinaryTerminalProfileCompiler.profile (prepare input) state K outer) slot K scalar)

theorem sample_canonical (input : BinaryFourParameters.Input) (state : State) (hInput : input.Canonical)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    ∀ j, CanonicalWord ((sample input state K outer scalar slot).read j) := by
  have hRow := BinarySegmentPoint.sample_canonical _ slot K scalar
    (BinaryTerminalProfileCompiler.profile_canonical _ state (prepare_canonical input hInput) hState K outer)
  intro j
  unfold sample reflect
  rw [FixedArrayTable.read_ofFn]
  fin_cases j
  · exact opcode_canonical .sub _ _ hInput.2.1 (hRow 0)
  · exact opcode_canonical .sub _ _ hInput.2.2.1 (hRow 1)
  · exact opcode_canonical .sub _ _ hInput.2.2.2.1 (hRow 2)
  · change CanonicalWord BinaryRationalOpcode.zero
    exact ⟨BinaryRationalOpcode.zero_valid,by decide⟩

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (state : State)
    (terminal : RationalTerminalResources) (hInput : input.Canonical) (hRef : input.Refines source)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) (hData : DataRefines (prepare input) state terminal)
    (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) (j : Fin 4) :
    value ((sample input state K outer scalar slot).read j) =
      (RationalAffineAllocation.reflectAppend source.originalLengths).value ((terminal.profile K outer).point K slot scalar) j := by
  have hTable := BinaryTerminalProfileCompiler.profile_canonical _ state (prepare_canonical input hInput) hState K outer
  have hTableRef := BinaryTerminalProfileCompiler.profile_refines _ state terminal (prepare_canonical input hInput) hState hData K outer
  have hRow := BinarySegmentPoint.sample_canonical _ slot K scalar hTable
  have hValues := BinarySegmentPoint.sample_value _ _ hTable hTableRef slot K scalar
  have he := reflect_value input source hInput hRef _ hRow j
  apply he.trans
  apply congrArg (fun row => (RationalAffineAllocation.reflectAppend source.originalLengths).value row j)
  funext field
  exact hValues field

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput) (state : State)
    (terminal : RationalTerminalResources) (hInput : input.Canonical) (hRef : input.Refines source)
    (hCase : source.w < (1-source.p)*source.ell) (hState : ∀ j, CanonicalWord (state.resource.read j))
    (hData : DataRefines (prepare input) state terminal) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    FullBudget (source.B : ℝ) (fun j => (value ((sample input state K outer scalar slot).read j) : ℝ)) := by
  have hSystem := prepare_refines input source hInput hRef hCase
  have hM : terminal.M = source.reflectedBudget := hData.1.symm.trans hSystem.1
  have hLong : terminal.long = source.originalLengths := by
    funext field
    exact (hData.2.1 field).symm.trans (originalLengths_value input source hRef field)
  have hTable := terminal.profile_endpoints K outer
  have hBudget := (terminal.profile K outer).point_fullBudget K hTable slot scalar
  have hBox := (terminal.profile K outer).point_inBox K _ (terminal.profile_box K outer) slot scalar
  rw [hM] at hBudget
  rw [hLong] at hBox
  have hResult := RationalAffineAllocation.reflectAppend_fullBudget source.originalLengths
    (source.reflection_budget_sum hCase) hBudget hBox
  have hValues : (fun j => (value ((sample input state K outer scalar slot).read j) : ℝ)) =
      (RationalAffineAllocation.reflectAppend source.originalLengths).real.value
        (fun field => ((terminal.profile K outer).point K slot scalar field : ℝ)) := by
    rw [← RationalAffineAllocation.value_real]
    funext j
    exact congrArg (fun q : ℚ => (q : ℝ)) (sample_value input source state terminal hInput hRef hState hData K outer scalar slot j)
  rw [hValues]
  exact hResult

theorem sample_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput) (state : State)
    (terminal : RationalTerminalResources) (hInput : input.Canonical) (hRef : input.Refines source)
    (hState : ∀ j, CanonicalWord (state.resource.read j)) (hData : DataRefines (prepare input) state terminal)
    (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((sample input state K outer scalar slot).read j) : ℝ)) := by
  have hLong : terminal.long = source.originalLengths := by
    funext field
    exact (hData.2.1 field).symm.trans (originalLengths_value input source hRef field)
  have hBox := (terminal.profile K outer).point_inBox K _ (terminal.profile_box K outer) slot scalar
  rw [hLong] at hBox
  have hResult := RationalAffineAllocation.reflectAppend_box source.originalLengths (by exact_mod_cast source.ell_pos.le : (0 : ℝ) ≤ (source.ell : ℝ)) hBox
  have hValues : (fun j => (value ((sample input state K outer scalar slot).read j) : ℝ)) =
      (RationalAffineAllocation.reflectAppend source.originalLengths).real.value
        (fun field => ((terminal.profile K outer).point K slot scalar field : ℝ)) := by
    rw [← RationalAffineAllocation.value_real]
    funext j
    exact congrArg (fun q : ℚ => (q : ℝ)) (sample_value input source state terminal hInput hRef hState hData K outer scalar slot j)
  rw [hValues]
  exact hResult

end Blotto.BinaryReflectedTerminalEmission
