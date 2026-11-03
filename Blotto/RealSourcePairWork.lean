import Blotto.RealCallbackWork
import Blotto.RealLottoActivePhase

/-! The shared pair-arithmetic contribution along the global source is
linear in its callback cap. List/control and persistent resource-array
operations are deliberately outside this local arithmetic allowance. -/

namespace Blotto

noncomputable def realPairCallbackCharge {n : ℕ} {L : Allocation n} (cursor : RealArrayCursor L) : ℕ :=
  match realArrayStep cursor with
  | .done _ => 0
  | .ask _ _ _ _ => RealPairProgram.preparationWork

theorem realPairCallbackCharge_bound {n : ℕ} {L : Allocation n} (cursor : RealArrayCursor L) :
    realPairCallbackCharge cursor ≤ 96 := by
  unfold realPairCallbackCharge
  cases realArrayStep cursor
  · exact Nat.zero_le _
  · rw [RealPairProgram.preparationWork_eq]

theorem realSourcePairWork_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (realActiveArrayMachine i.length).callbackWork realPairCallbackCharge (n - 1) seed
      (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) 0 (Nat.zero_le _) ≤
      96 * ((n - 1) + 1) :=
  (realActiveArrayMachine i.length).callbackWork_rank realPairCallbackCharge 96 realPairCallbackCharge_bound _ _ _

theorem realSourcePairWork_update_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (realActiveArrayMachine i.length).callbackWork realPairCallbackCharge (n - 1) seed
      (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) 0 (Nat.zero_le _) ≤
      96 * (n - 1) := by
  apply (realActiveArrayMachine i.length).callbackWork_request_rank realPairCallbackCharge 96 realPairCallbackCharge_bound
  intro cursor x hs
  change realArrayStep cursor = .done x at hs
  unfold realPairCallbackCharge
  rw [hs]

end Blotto
