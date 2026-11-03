import Blotto.RealCallbackWork
import Blotto.RealLottoActivePhase

/-! Only a reached pending cursor executes the pair-store program. This
observer follows the actual indexed source, including exhausted input buffers.
It prices the resource/register component separately from source control. -/

namespace Blotto
open scoped Classical

def realResourceStoreCharge {n : ℕ} {L : Allocation n} : RealArrayCursor L → ℕ
  | .ready _ _ => 0
  | .pending _ _ _ _ _ _ _ => 1

theorem realResourceStoreCharge_bound {n : ℕ} {L : Allocation n} (cursor : RealArrayCursor L) :
    realResourceStoreCharge cursor ≤ 1 := by cases cursor <;> simp [realResourceStoreCharge]

theorem realResourceStores_ready_bound {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ArrayResourceState L) (C : ℕ) (seed : Fin C → ℝ) :
    (realActiveArrayMachine L).callbackWork realResourceStoreCharge C seed (.ready fuel s) 0 (Nat.zero_le _) ≤ fuel := by
  unfold RealStateMachine.callbackWork
  simp only [realResourceStoreCharge, Nat.zero_add]
  rw [show (realActiveArrayMachine L).step (.ready fuel s) = realArrayReadyStep fuel s from rfl]
  cases hs : realArrayReadyStep fuel s with
  | done value => exact Nat.zero_le _
  | ask p hp upper lower =>
    have hProgress := realArrayReadyStep_progress fuel s
    rw [hs] at hProgress
    dsimp only
    split
    · rename_i hRead
      split
      · have h := (realActiveArrayMachine L).callbackWork_visits realResourceStoreCharge 1
          realResourceStoreCharge_bound C seed upper 1 (by omega)
        have hv := (realActiveArrayMachine L).visits_bound C seed upper 1 (by omega)
        change RealArrayCursor.fuel upper < fuel ∧ RealArrayCursor.fuel lower < fuel at hProgress
        change _ ≤ RealArrayCursor.fuel upper + 1 at hv
        omega
      · have h := (realActiveArrayMachine L).callbackWork_visits realResourceStoreCharge 1
          realResourceStoreCharge_bound C seed lower 1 (by omega)
        have hv := (realActiveArrayMachine L).visits_bound C seed lower 1 (by omega)
        change RealArrayCursor.fuel upper < fuel ∧ RealArrayCursor.fuel lower < fuel at hProgress
        change _ ≤ RealArrayCursor.fuel lower + 1 at hv
        omega
    · exact Nat.zero_le _

noncomputable def realSourceStores {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) : ℕ :=
  (realActiveArrayMachine i.length).callbackWork realResourceStoreCharge (n - 1) seed
    (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) 0 (Nat.zero_le _)

theorem realSourceStores_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    realSourceStores i seed ≤ n - 1 := realResourceStores_ready_bound _ _ _ _

theorem realSourceResourceWrites_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    2 * realSourceStores i seed ≤ 2 * (n - 1) := Nat.mul_le_mul_left 2 (realSourceStores_bound i seed)

theorem realSourceStoreRamWork_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    20 * realSourceStores i seed ≤ 20 * (n - 1) := Nat.mul_le_mul_left 20 (realSourceStores_bound i seed)

theorem realSourceStoreScratchCopyWork_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    32 * realSourceStores i seed ≤ 32 * (n - 1) := Nat.mul_le_mul_left 32 (realSourceStores_bound i seed)

theorem realSourceStoreNativeCopyWork_bound {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (2 * n + 30) * realSourceStores i seed ≤ (2 * n + 30) * (n - 1) :=
  Nat.mul_le_mul_left _ (realSourceStores_bound i seed)

end Blotto
