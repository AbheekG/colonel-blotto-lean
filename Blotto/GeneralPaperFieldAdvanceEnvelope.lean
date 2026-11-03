import Blotto.GeneralPaperEpochInitialFamilyPrice

/-! Uniform prices for the eight local level additions. Actual retained
cache descriptors supply the common length cap in the caller. The global
reference word is distinct from each array's derived index-control word.
-/
namespace Blotto.GeneralPaperFieldAdvanceEnvelope
open GeneralPaperEpochFieldState
open GeneralPaperEpochFieldAdvancePrice (total total_mono)
set_option autoImplicit false
set_option maxHeartbeats 4000000

def profile (price : ℕ → ℕ) (W m lambda k Qv B : ℕ) : ℕ :=
  8*GeneralPaperEpochLevelPrice.profile price W m lambda k Qv B+256*W

def arithmeticProfile (B : ℕ) : ℕ := 8*GeneralPaperEpochLevelPrice.arithmeticProfile B+256

theorem level_profile_mono (price : ℕ → ℕ) (W m lambda k Qv n N : ℕ) (hN : n≤N) :
    GeneralPaperEpochLevelPrice.profile price W m lambda k Qv n≤GeneralPaperEpochLevelPrice.profile price W m lambda k Qv N := by
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hN)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 44 (by omega : n+1≤N+1)) (GeneralPaperPlanProfileMonotonicity.array_word W n N hN))

theorem bound {k : ℕ} (price : ℕ → ℕ) (W m lambda Qv B : ℕ) (state : State k)
    (hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : state.plan.pCells.partition.count≤B) (hq : state.plan.qCells.partition.count≤B)
    (hl : state.plan.lambdaCells.partition.count≤B) (hm : state.plan.muCells.partition.count≤B) :
    GeneralPaperEpochFieldAdvancePrice.profile price W m lambda Qv state≤profile price W m lambda k Qv B := by
  have h := Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (level_profile_mono price W m lambda k Qv _ B hS) (level_profile_mono price W m lambda k Qv _ B hS)
    (level_profile_mono price W m lambda k Qv _ B hS) (level_profile_mono price W m lambda k Qv _ B hS)
    (level_profile_mono price W m lambda k Qv _ B hp) (level_profile_mono price W m lambda k Qv _ B hq)
    (level_profile_mono price W m lambda k Qv _ B hl) (level_profile_mono price W m lambda k Qv _ B hm)) (256*W)
  exact h.trans_eq (by unfold profile total; ring)

theorem level_arithmetic_mono (n N : ℕ) (hN : n≤N) :
    GeneralPaperEpochLevelPrice.arithmeticProfile n≤GeneralPaperEpochLevelPrice.arithmeticProfile N := by
  exact Nat.add_le_add (Nat.mul_le_mul_right 34 hN) (Nat.mul_le_mul_left 44 (by omega))

theorem arithmetic_bound {k : ℕ} (B : ℕ) (state : State k)
    (hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : state.plan.pCells.partition.count≤B) (hq : state.plan.qCells.partition.count≤B)
    (hl : state.plan.lambdaCells.partition.count≤B) (hm : state.plan.muCells.partition.count≤B) :
    GeneralPaperEpochFieldAdvancePrice.arithmeticProfile state≤arithmeticProfile B := by
  have h := Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (level_arithmetic_mono _ B hS) (level_arithmetic_mono _ B hS)
    (level_arithmetic_mono _ B hS) (level_arithmetic_mono _ B hS)
    (level_arithmetic_mono _ B hp) (level_arithmetic_mono _ B hq)
    (level_arithmetic_mono _ B hl) (level_arithmetic_mono _ B hm)) 256
  exact h.trans_eq (by unfold arithmeticProfile total; ring)

end Blotto.GeneralPaperFieldAdvanceEnvelope
