import Blotto.WordMachineSerialRun
import Blotto.RationalNestedResourceMachine

/-! The retained reflected resource sampler's indexed execution decomposes
into its invariant phase and selected terminal continuation with unchanged
reader/cap and exact returned position. -/

namespace Blotto.RationalNestedResourceSystem

theorem machine_run_serial (source : RationalNestedResourceSystem) (K N : ℕ) (outer scalar : Fin K → Bool)
    (bits : Fin N → Bool) :
    (source.machine K outer scalar).run N source.samplingStart bits =
      WordStateMachine.handoff N (source.phase.run N source.start bits)
        (fun phase pos hp => (source.continuationMachine K outer scalar phase).runCursorIndexed N bits
          (.state (source.continuationStart K outer phase)) pos hp) := by
  rw [WordStateMachine.run_eq_numeric]
  change (source.phase.serial (source.continuationMachine K outer scalar) (source.continuationStart K outer) 17 _).runCursorIndexed
      N bits ((WordCursor.state source.start).mapState SerialState.source) 0 (Nat.zero_le N) = _
  rw [WordStateMachine.serial_source_run]
  rw [WordStateMachine.run_eq_numeric]
  rfl

end Blotto.RationalNestedResourceSystem
