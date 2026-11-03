import Blotto.BinarySeedPreparationSpace

/-! Proof identities for emitting absolute frame depths during execution.
These identities do not traverse traces in the measured producers. -/
namespace Blotto.BinaryTraceDepth
open BinarySeedPreparationSpace
set_option autoImplicit false

theorem under_compose (first second : ℕ) (trace : Trace) :
    under first (under second trace) = under (first+second) trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [under,shiftEvent,Nat.add_assoc] at ih ⊢ <;> exact ih

theorem under_append (depth : ℕ) (first second : Trace) :
    under depth (first++second) = under depth first++under depth second := by
  simp only [under,List.map_append]

theorem under_zero (trace : Trace) : under 0 trace = trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [under,shiftEvent] at ih ⊢ <;> exact ih

end Blotto.BinaryTraceDepth
