import Blotto.WordMachineCallbackWork
import Blotto.RationalResourceMachine

/-! Selected rational cursors materialize exactly one pair-store program.
Weighted callback work follows the native indexed controller, including caps
and all fair-bit paths. Bit arithmetic and source-control costs are separate. -/

namespace Blotto

def rationalResourceStoreCharge {n : ℕ} {L : Fin n → ℚ} : RationalResourceCursor L → ℕ
  | .ready _ => 0
  | .selected _ _ _ _ _ _ => 1

theorem rationalResourceStoreCharge_bound {n : ℕ} {L : Fin n → ℚ} (cursor : RationalResourceCursor L) :
    rationalResourceStoreCharge cursor ≤ 1 := by cases cursor <;> simp [rationalResourceStoreCharge]

def rationalSourceStores {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) : ℕ :=
  (rationalResourceMachine L).runCallbackWork rationalResourceStoreCharge R
    (.ready (RationalActiveResources.initial L r)) bits

theorem rationalSourceStores_bound {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) :
    rationalSourceStores L r R bits ≤ n - 1 := by
  have h := (rationalResourceMachine L).runCallbackWork_zero_initial_rank rationalResourceStoreCharge 1
    rationalResourceStoreCharge_bound R (.ready (RationalActiveResources.initial L r)) rfl bits
  simp only [Nat.one_mul] at h
  exact h.trans (rationalResourceMachine_initial_rank L r)

theorem rationalSourceResourceWrites_bound {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) :
    2 * rationalSourceStores L r R bits ≤ 2 * (n - 1) :=
  Nat.mul_le_mul_left 2 (rationalSourceStores_bound L r R bits)

theorem rationalSourceStoreRamWork_bound {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) :
    20 * rationalSourceStores L r R bits ≤ 20 * (n - 1) :=
  Nat.mul_le_mul_left 20 (rationalSourceStores_bound L r R bits)

theorem rationalSourceStoreScratchCopyWork_bound {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) :
    32 * rationalSourceStores L r R bits ≤ 32 * (n - 1) :=
  Nat.mul_le_mul_left 32 (rationalSourceStores_bound L r R bits)

theorem rationalSourceStoreNativeCopyWork_bound {n : ℕ} (L r : Fin n → ℚ) (R : ℕ) (bits : Fin R → Bool) :
    (2 * n + 30) * rationalSourceStores L r R bits ≤ (2 * n + 30) * (n - 1) :=
  Nat.mul_le_mul_left _ (rationalSourceStores_bound L r R bits)

end Blotto
