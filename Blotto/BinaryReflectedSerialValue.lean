import Blotto.BinaryReflectedSerialSelection
import Blotto.RationalNestedSerialRun

/-! Exact native reflected emission on a selected reached terminal state is the
original source continuation point. No alternate marginal law is substituted. -/

namespace Blotto.BinaryReflectedSerialValue
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun BinaryReflectedPhaseRefinement

theorem emission_value (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity) (hSuccess : (setupRun input hC N bits).1=some result)
    (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) (j : Fin 4) :
    value ((BinaryReflectedTerminalEmission.sample input result.state K outer scalar slot).read j) =
      (RationalAffineAllocation.reflectAppend source.originalLengths).value
        ((((source.reflectedResourceSystem hCase).terminalData
          (phaseResult input source hC hr hCase N bits result hSuccess)).profile K outer).point K slot scalar) j :=
  BinaryReflectedTerminalEmission.sample_value input source result.state _ hC hr result.canonical
    (BinaryReachedTerminal.terminal_data_refines input source hC hr hCase N bits result hSuccess) K outer scalar slot j

noncomputable def sourceRow (row : FixedArrayTable 4 SignedWord) : Fin 4 → ℚ := fun j => value (row.read j)

end Blotto.BinaryReflectedSerialValue
