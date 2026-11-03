import Blotto.GeneralPaperRoundedLosses
import Blotto.GeneralPaperTrajectoryParameters

/-! Actual dyadic source parameters from the accuracy exponent already used
by the score and trajectory constructors. Powers are computed by repeated
doubling. The regret slack is proved for the actual constructed horizon T.
Bit prices, precision selection, alphabet construction and the complete
source execution are separate obligations, not asserted here.
-/
namespace Blotto.GeneralPaperSourceParameters
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Parameters where
  z : ℚ
  eta : ℚ
  nu : ℚ
  theta : ℚ
  meshDenominator : ℕ
  summarySize : ℕ
  work : ℕ

def prepare (k : ℕ) : Parameters :=
  let zd := powerRun (11+k)
  let ed := powerRun (25+k)
  let nd := powerRun (32+k)
  let td := powerRun (29+k)
  let summary := powerRun (34+k)
  ⟨1/(zd.power:ℚ),1/(ed.power:ℚ),1/(nd.power:ℚ),1/(td.power:ℚ),td.power,summary.power,
    zd.work+ed.work+nd.work+td.work+summary.work+64⟩

theorem data (k : ℕ) :
    (prepare k).z=1/(2:ℚ)^(11+k) ∧ (prepare k).eta=1/(2:ℚ)^(25+k) ∧
    (prepare k).nu=1/(2:ℚ)^(32+k) ∧ (prepare k).theta=1/(2:ℚ)^(29+k) ∧
    (prepare k).meshDenominator=2^(29+k) ∧ (prepare k).summarySize=2^(34+k) := by
  simp only [prepare, (power_data _).1, Nat.cast_pow, Nat.cast_ofNat, and_self]

theorem positive (k : ℕ) : 0<(prepare k).z ∧ 0<(prepare k).eta ∧ 0<(prepare k).nu ∧ 0<(prepare k).theta := by
  have h := data k
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2.1]
  exact ⟨by positivity,by positivity,by positivity,by positivity⟩

theorem eta_z (k : ℕ) : (prepare k).eta=(prepare k).z/16384 := by
  rw [(data k).1,(data k).2.1]
  simp only [pow_add]
  norm_num
  ring

theorem theta_eta (k : ℕ) : (prepare k).theta=(prepare k).eta/16 := by
  rw [(data k).2.1,(data k).2.2.2.1]
  simp only [pow_add]
  norm_num
  ring

theorem nu_eta (k : ℕ) : (prepare k).nu=(prepare k).eta/128 := by
  rw [(data k).2.1,(data k).2.2.1]
  simp only [pow_add]
  norm_num
  ring

theorem theta_mesh (k : ℕ) : (prepare k).theta=1/((prepare k).meshDenominator:ℚ) := rfl

theorem mesh_positive (k : ℕ) : 0<(prepare k).meshDenominator := by rw [(data k).2.2.2.2.1]; positivity

theorem summary_exact (k : ℕ) : ((prepare k).summarySize:ℚ)=4/(prepare k).nu := by
  rw [(data k).2.2.1,(data k).2.2.2.2.2]
  push_cast
  simp only [div_eq_mul_inv, one_mul, inv_inv, pow_add]
  norm_num
  ring

theorem eta_upper (k : ℕ) : (prepare k).eta ≤ 1 := by
  rw [(data k).2.1]
  exact (one_div_le_one_div_of_le (by norm_num : (0:ℚ)<1) (one_le_pow₀ (by norm_num : (1:ℚ)≤2))).trans_eq (by norm_num)

theorem eta_theta (k : ℕ) : (prepare k).eta*(prepare k).theta ≤ 1 := by
  have he := eta_upper k
  have hp := (positive k).2.1
  rw [theta_eta]
  nlinarith

theorem loss_error (k : ℕ) : 25*(prepare k).nu+3*(prepare k).theta=49*(prepare k).eta/128 := by
  rw [nu_eta,theta_eta]
  ring

theorem optimizer_error (k : ℕ) :
    (prepare k).eta+40*(prepare k).nu+4*(prepare k).theta=25*(prepare k).eta/16 := by
  rw [nu_eta,theta_eta]
  ring

theorem period_eta (lambda k : ℕ) :
    ((GeneralPaperTrajectoryParameters.prepare lambda k).period:ℚ)*(prepare k).eta=1/16384 := by
  rw [GeneralPaperTrajectoryParameters.period_power,(data k).2.1]
  push_cast
  simp only [pow_add]
  norm_num
  field_simp
  <;> ring

theorem scaled_horizon (lambda k : ℕ) :
    ((lambda:ℝ)+2)/16 ≤ ((prepare k).eta:ℝ)^2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows := by
  have hl := GeneralPaperTrajectoryParameters.rows_lower lambda k
  have hr : (16777216:ℝ)*((lambda:ℝ)+2)*((GeneralPaperTrajectoryParameters.prepare lambda k).period:ℝ)^2 ≤
      (GeneralPaperTrajectoryParameters.prepare lambda k).rows := by exact_mod_cast hl
  have hp : ((GeneralPaperTrajectoryParameters.prepare lambda k).period:ℝ)*((prepare k).eta:ℝ)=1/16384 := by
    have he := congrArg (fun q : ℚ => (q:ℝ)) (period_eta lambda k)
    push_cast at he
    norm_num at he
    exact he
  have hsq : ((prepare k).eta:ℝ)^2*((GeneralPaperTrajectoryParameters.prepare lambda k).period:ℝ)^2=1/268435456 := by
    calc
      _ = (((GeneralPaperTrajectoryParameters.prepare lambda k).period:ℝ)*((prepare k).eta:ℝ))^2 := by ring
      _ = _ := by rw [hp]; norm_num
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg ((prepare k).eta:ℝ))
  nlinarith only [hm,hsq]

theorem initial_regret_slack (lambda k : ℕ) :
    4*((lambda:ℝ)+1)/(((prepare k).eta:ℝ)*(GeneralPaperTrajectoryParameters.prepare lambda k).rows) <
      64*((prepare k).eta:ℝ) := by
  have hh := scaled_horizon lambda k
  have he : (0:ℝ) < (prepare k).eta := by exact_mod_cast (positive k).2.1
  have ht : (0:ℝ) < (GeneralPaperTrajectoryParameters.prepare lambda k).rows :=
    by exact_mod_cast GeneralPaperTrajectoryParameters.rows_positive lambda k
  apply (div_lt_iff₀ (mul_pos he ht)).mpr
  nlinarith only [hh]

noncomputable def gamma (lambda k : ℕ) : ℝ :=
  4*((lambda:ℝ)+1)/(((prepare k).eta:ℝ)*(GeneralPaperTrajectoryParameters.prepare lambda k).rows)+
    20*((prepare k).eta:ℝ)+8*(25*((prepare k).nu:ℝ)+3*((prepare k).theta:ℝ))+
    2*(((prepare k).eta:ℝ)+40*((prepare k).nu:ℝ)+4*((prepare k).theta:ℝ))

theorem gamma_bound (lambda k : ℕ) : gamma lambda k < (1443:ℝ)/16*((prepare k).eta:ℝ) := by
  have hi := initial_regret_slack lambda k
  have he : 25*((prepare k).nu:ℝ)+3*((prepare k).theta:ℝ)=49*((prepare k).eta:ℝ)/128 :=
    by exact_mod_cast loss_error k
  have ho : ((prepare k).eta:ℝ)+40*((prepare k).nu:ℝ)+4*((prepare k).theta:ℝ)=25*((prepare k).eta:ℝ)/16 :=
    by exact_mod_cast optimizer_error k
  unfold gamma
  linarith

theorem gamma_source_slack (lambda k : ℕ) : gamma lambda k < ((prepare k).z:ℝ)/64 := by
  have hg := gamma_bound lambda k
  have he : ((prepare k).eta:ℝ)=((prepare k).z:ℝ)/16384 := by exact_mod_cast eta_z k
  have hp : (0:ℝ) < (prepare k).z := by exact_mod_cast (positive k).1
  linarith

theorem prepare_work (k : ℕ) : (prepare k).work=8*(131+5*k)+74 := by
  simp only [prepare, (power_data _).2.2]
  omega

end Blotto.GeneralPaperSourceParameters
