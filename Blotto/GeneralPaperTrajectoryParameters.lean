import Blotto.GeneralPaperScoreScaleParameters

/-! Selected R263 full-trajectory lengths. The epoch count is the least
power of two above the displayed constructed integer target. The period is
16*K, so the actual total T is a power of two and K divides T. No acceptance
gate, subsampling or restart parameter is introduced.
-/
namespace Blotto.GeneralPaperTrajectoryParameters
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Parameters where
  period : ℕ
  epochs : ℕ
  rows : ℕ
  rowBits : ℕ
  work : ℕ

def prepare (lambda k : ℕ) : Parameters :=
  let period := powerRun (11+k)
  let factor := powerRun (35+k)
  let epochs := GeneralPaperPowerCeiling.ceiling ((lambda+2)*factor.power)
  ⟨period.power,epochs.power,epochs.power*period.power,epochs.doublings+period.doublings,
    period.work+factor.work+epochs.work+24⟩

theorem period_power (lambda k : ℕ) : (prepare lambda k).period=2^(11+k) := (power_data (11+k)).1

theorem period_labels (m lambda k : ℕ) :
    (prepare lambda k).period=16*(GeneralPaperScoreScaleParameters.prepare m k).K := by
  rw [period_power,label_power]
  simp only [pow_add]
  norm_num
  ring

theorem rows_product (lambda k : ℕ) :
    (prepare lambda k).rows=(prepare lambda k).epochs*(prepare lambda k).period := rfl

theorem epochs_lower (lambda k : ℕ) :
    (lambda+2)*2^(35+k)≤(prepare lambda k).epochs := by
  change (lambda+2)*2^(35+k)≤(GeneralPaperPowerCeiling.ceiling ((lambda+2)*(powerRun (35+k)).power)).power
  rw [← (power_data (35+k)).1]
  exact GeneralPaperPowerCeiling.ceiling_lower _

theorem epochs_upper (lambda k : ℕ) :
    (prepare lambda k).epochs<2*((lambda+2)*2^(35+k)) := by
  have ht : 0<(lambda+2)*(powerRun (35+k)).power := by rw [(power_data (35+k)).1]; positivity
  change (GeneralPaperPowerCeiling.ceiling ((lambda+2)*(powerRun (35+k)).power)).power<2*((lambda+2)*2^(35+k))
  rw [← (power_data (35+k)).1]
  exact GeneralPaperPowerCeiling.ceiling_upper _ ht

theorem epochs_dyadic (lambda k : ℕ) : ∃ r,(prepare lambda k).epochs=2^r := by
  exact ⟨_,GeneralPaperPowerCeiling.ceiling_power _⟩

theorem rows_power (lambda k : ℕ) : (prepare lambda k).rows=2^(prepare lambda k).rowBits := by
  unfold prepare
  dsimp only
  rw [GeneralPaperPowerCeiling.ceiling_power,(power_data (11+k)).1,(power_data (11+k)).2.1]
  simp only [pow_add]

theorem rows_positive (lambda k : ℕ) : 0<(prepare lambda k).rows := by
  rw [rows_power]
  exact Nat.two_pow_pos _

theorem labels_divide_rows (m lambda k : ℕ) :
    (GeneralPaperScoreScaleParameters.prepare m k).K∣(prepare lambda k).rows := by
  refine ⟨(prepare lambda k).epochs*16,?_⟩
  rw [rows_product,period_labels m lambda k]
  ring

theorem epoch_target (lambda k : ℕ) :
    2^24*(lambda+2)*(prepare lambda k).period=(lambda+2)*2^(35+k) := by
  rw [period_power]
  simp only [pow_add]
  norm_num
  ring

theorem rows_lower (lambda k : ℕ) :
    2^24*(lambda+2)*(prepare lambda k).period^2≤(prepare lambda k).rows := by
  have he := epochs_lower lambda k
  rw [← epoch_target] at he
  have h := Nat.mul_le_mul_right (prepare lambda k).period he
  rw [rows_product]
  convert h using 1 <;> ring

theorem rows_upper (lambda k : ℕ) :
    (prepare lambda k).rows<2^25*(lambda+2)*(prepare lambda k).period^2 := by
  have he := epochs_upper lambda k
  rw [← epoch_target] at he
  have hp : 0<(prepare lambda k).period := by rw [period_power]; exact Nat.two_pow_pos _
  have h := Nat.mul_lt_mul_of_pos_right he hp
  rw [rows_product]
  convert h using 1 <;> norm_num <;> ring

theorem rowBits_bound (lambda k : ℕ) :
    (prepare lambda k).rowBits≤binaryWordWidth ((lambda+2)*2^(35+k))+(11+k) := by
  have hd := GeneralPaperPowerCeiling.loop_depth ((lambda+2)*(powerRun (35+k)).power) 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling ((lambda+2)*(powerRun (35+k)).power)).doublings≤_ at hd
  change (GeneralPaperPowerCeiling.ceiling ((lambda+2)*(powerRun (35+k)).power)).doublings+(powerRun (11+k)).doublings≤_
  rw [(power_data (11+k)).2.1]
  simpa only [(power_data (35+k)).1] using Nat.add_le_add_right hd (11+k)

theorem prepare_work (lambda k : ℕ) : (prepare lambda k).work≤
    8*(11+k)+8*(35+k)+12*binaryWordWidth ((lambda+2)*2^(35+k))+30 := by
  have hp := (power_data (11+k)).2.2
  have hf := (power_data (35+k)).2.2
  have he := GeneralPaperPowerCeiling.ceiling_work ((lambda+2)*(powerRun (35+k)).power)
  simp only [(power_data (35+k)).1] at he
  change (powerRun (11+k)).work+(powerRun (35+k)).work+
    (GeneralPaperPowerCeiling.ceiling ((lambda+2)*(powerRun (35+k)).power)).work+24≤_
  rw [(power_data (35+k)).1]
  omega

theorem quantizer_correct {m : ℕ} (lambda k : ℕ)
    (rows : FixedArrayTable (prepare lambda k).rows (FixedArrayTable m ℚ)) (budget : ℝ)
    (hRows : ∀ i,Feasible budget (fun j => ((rows.read i).read j:ℝ))) :
    GeneralPaperRowQuantizer.Correct rows
      (GeneralPaperRowQuantizer.buildDivisible (rows_positive lambda k) (labels_positive m k)
        (labels_divide_rows m lambda k) rows) (rows_positive lambda k) (labels_positive m k) budget :=
  GeneralPaperRowQuantizer.divisible_correct (rows_positive lambda k) (labels_positive m k)
    (labels_divide_rows m lambda k) rows budget hRows

end Blotto.GeneralPaperTrajectoryParameters
