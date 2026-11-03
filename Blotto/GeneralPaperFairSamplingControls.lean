import Blotto.GeneralPaperNativeFairSamplerPrice

/-! Retain source row-count/bit controls and construct the selected shift
count by native doubling once. No logarithm, input encoding or power
constructor is called by a draw. Cost observers may use erased bounds. -/
namespace Blotto.GeneralPaperFairSamplingControls
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Controls where
  rowBits : ℕ
  shiftBits : ℕ
  rows : ℕ
  shifts : ℕ

def run (primitive : ℕ → ℕ) (A k : ℕ) (trajectory : GeneralPaperTrajectoryParameters.Parameters) : Controls×ℕ :=
  let exponent := k+6
  let shift := GeneralPaperDyadicPowerBits.run primitive A exponent
  (⟨trajectory.rowBits,shift.1.doublings,trajectory.rows,shift.1.power⟩,
    shift.2+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) k 6+64*A)

theorem row_power (primitive : ℕ → ℕ) (A lambda k : ℕ) (trajectory : GeneralPaperTrajectoryParameters.Parameters)
    (ht : trajectory=GeneralPaperTrajectoryParameters.prepare lambda k) :
    (run primitive A k trajectory).1.rows=2^(run primitive A k trajectory).1.rowBits := by
  exact ht ▸ GeneralPaperTrajectoryParameters.rows_power lambda k

theorem shift_power (primitive : ℕ → ℕ) (A k : ℕ) (trajectory : GeneralPaperTrajectoryParameters.Parameters) :
    (run primitive A k trajectory).1.shifts=2^(run primitive A k trajectory).1.shiftBits := by
  simp only [run,GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data (k+6)).1,
    (GeneralPaperScoreScaleParameters.power_data (k+6)).2.1]

theorem selected_shifts (primitive : ℕ → ℕ) (A k : ℕ) (trajectory : GeneralPaperTrajectoryParameters.Parameters) :
    (run primitive A k trajectory).1.shifts=GeneralPaperNativeSelectedSecurity.count k := by
  simp only [run,GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data (k+6)).1,
    GeneralPaperNativeSelectedSecurity.count_power]

theorem selected_shift_bits (primitive : ℕ → ℕ) (A k : ℕ) (trajectory : GeneralPaperTrajectoryParameters.Parameters) :
    (run primitive A k trajectory).1.shiftBits=k+6 := by
  simp only [run,GeneralPaperDyadicPowerBits.data,(GeneralPaperScoreScaleParameters.power_data (k+6)).2.1]

theorem arithmetic_work (k : ℕ) (trajectory : GeneralPaperTrajectoryParameters.Parameters) :
    (run (fun _ => 1) 1 k trajectory).2≤128*(k+7)+66 := by
  have hh := GeneralPaperDyadicPowerBits.work (fun _ => 1) (fun _ _ _ => le_rfl) 1 (k+6)
  simp only [run,GeneralPaperNaturalPrimitivePrice.binary]
  omega

end Blotto.GeneralPaperFairSamplingControls
