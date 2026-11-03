import Blotto.GeneralPaperStoredRecordReadWork

/-! The actual fresh-bit countdown has linear work in the loaded count up
to address metadata, including reversing/padding the final bit buffer.
Count/control prefixes are bounded; no new unary ruler is reconstructed. -/
namespace Blotto.GeneralPaperStoredFreshWork
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def stepBound (model : RationalCostModel) (A : ℕ) : ℕ := 5 * model.rat (A + 2) + 128 * (A + 1) + 4

def bound (model : RationalCostModel) (A fuel acc : ℕ) : ℕ :=
  fuel * stepBound model A + 4 * acc + 6 + 64 * (A + 1)

theorem previous_work (model : RationalCostModel) (A fuel : ℕ) (hFuel : fuel < 2 ^ A) :
    (GeneralPaperStoredFreshCollect.previous model A fuel).2 ≤ 5 * model.rat (A + 2) + 64 * (A + 1) := by
  have hWidth : binaryWordWidth fuel ≤ A + 1 := binaryWordWidth_le_of_lt_pow (by omega)
    (hFuel.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ A)))
  have hPrev := binaryWordWidth_mono (Nat.sub_le fuel 1)
  exact GeneralPaperStoredFreshCollect.previous_work model A fuel (A + 2)
    (by unfold GeneralPaperNaturalScalarStep.word; omega) (by change 2 ≤ A + 2; omega)
    (by unfold GeneralPaperNaturalScalarStep.word; omega)

theorem price_bound (model : RationalCostModel) (A fuel acc : ℕ) (hFuel : fuel < 2 ^ A) :
    GeneralPaperStoredFreshCollect.price model A fuel acc ≤ bound model A fuel acc := by
  induction fuel generalizing acc with
  | zero => simp only [GeneralPaperStoredFreshCollect.price,bound,Nat.zero_mul,Nat.zero_add,le_rfl]
  | succ fuel ih =>
    have hStep := previous_work model A (fuel + 1) hFuel
    have hLater := ih (acc + 1) (by omega)
    simp only [GeneralPaperStoredFreshCollect.price]
    unfold bound stepBound at *
    nlinarith only [hStep,hLater]

theorem collect_work {S : Type*} (model : RationalCostModel) (A fuel : ℕ) (acc : List Bool)
    (next : S → Bool × S) (state : S) (hFuel : fuel < 2 ^ A) :
    (GeneralPaperStoredFreshCollect.collect model A next fuel acc state).work ≤ bound model A fuel acc.length := by
  rw [GeneralPaperStoredFreshCollect.work]
  exact price_bound model A fuel acc.length hFuel

theorem read_work {S : Type*} (model : RationalCostModel) (A fuel : ℕ)
    (installed : GeneralPaperUnifiedDirectoryInstallation.Installed A) (next : S → Bool × S) (state : S)
    (hCount : (GeneralPaperStoredRulerRead.read model A installed).1 = some fuel) (hFuel : fuel < 2 ^ A) :
    (GeneralPaperStoredFreshRead.read model A installed next state).work ≤
      (GeneralPaperStoredRulerRead.read model A installed).2 + bound model A fuel 0 + 128 * (A + 1) := by
  rw [(GeneralPaperStoredFreshRead.on_count model A installed next state fuel hCount).2.2.2]
  exact Nat.add_le_add_right (Nat.add_le_add_left (price_bound model A fuel 0 hFuel) _) _

end Blotto.GeneralPaperStoredFreshWork
