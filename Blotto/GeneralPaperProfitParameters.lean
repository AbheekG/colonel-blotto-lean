import Blotto.GeneralPaperProfitApproximation

/-! Construct the paper's h_0, Q_prof, w_prof and B_prof from the already
selected accuracy/horizon and rounded-value denominator. Only arithmetic,
repeated doubling and comparisons are executed. This is parameter preparation;
grid/table/optimizer bit and space prices remain separate.
-/
namespace Blotto.GeneralPaperProfitParameters
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Parameters where
  height : ℕ
  leafCount : ℕ
  qProf : ℕ
  width : ℕ
  exponent : ℕ
  parameterWork : ℕ

def parameters (m lambda k Qv : ℕ) : Parameters :=
  let source := GeneralPaperSourceParameters.prepare k
  let trajectory := GeneralPaperTrajectoryParameters.prepare lambda k
  let leaves := GeneralPaperPowerCeiling.ceiling m
  let alphaDen := powerRun (25+k)
  let q := 2*trajectory.rows*Qv*source.meshDenominator
  let width := GeneralPaperPowerCeiling.ceiling (4*(leaves.doublings+1)*alphaDen.power)
  let exponent := GeneralPaperPowerCeiling.ceiling (4*q)
  ⟨leaves.doublings,leaves.power,q,width.power,exponent.doublings,
    source.work+trajectory.work+leaves.work+alphaDen.work+width.work+exponent.work+64⟩

theorem height_spec (m lambda k Qv : ℕ) : (parameters m lambda k Qv).height=(GeneralPaperPowerCeiling.ceiling m).doublings := rfl

theorem leaf_count_spec (m lambda k Qv : ℕ) : (parameters m lambda k Qv).leafCount=2^(parameters m lambda k Qv).height :=
  GeneralPaperPowerCeiling.ceiling_power m

theorem covers_fields (m lambda k Qv : ℕ) : m≤(parameters m lambda k Qv).leafCount := GeneralPaperPowerCeiling.ceiling_lower m

theorem leaf_count_upper (m lambda k Qv : ℕ) (hM : 0<m) : (parameters m lambda k Qv).leafCount<2*m :=
  GeneralPaperPowerCeiling.ceiling_upper m hM

theorem height_minimal (m lambda k Qv h : ℕ) (hM : m≤2^h) : (parameters m lambda k Qv).height≤h :=
  GeneralPaperPowerCeiling.ceiling_minimal m h hM

theorem qProf_spec (m lambda k Qv : ℕ) : (parameters m lambda k Qv).qProf=
    2*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*Qv*(GeneralPaperSourceParameters.prepare k).meshDenominator := rfl

theorem qProf_positive (m lambda k Qv : ℕ) (hQv : 0<Qv) : 0<(parameters m lambda k Qv).qProf := by
  rw [qProf_spec]
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (GeneralPaperTrajectoryParameters.rows_positive lambda k)) hQv)
    (GeneralPaperSourceParameters.mesh_positive k)

theorem qProf_identity (m lambda k Qv : ℕ) : ((parameters m lambda k Qv).qProf:ℚ)=
    2*((GeneralPaperTrajectoryParameters.prepare lambda k).rows:ℚ)*Qv/(GeneralPaperSourceParameters.prepare k).theta := by
  rw [qProf_spec,GeneralPaperSourceParameters.theta_mesh]
  push_cast
  simp only [div_eq_mul_inv,one_mul,inv_inv]

theorem width_spec (m lambda k Qv : ℕ) : (parameters m lambda k Qv).width=
    (GeneralPaperPowerCeiling.ceiling (4*((parameters m lambda k Qv).height+1)*(powerRun (25+k)).power)).power := rfl

theorem width_target_lower (m lambda k Qv : ℕ) : 4*((parameters m lambda k Qv).height+1)*2^(25+k)≤(parameters m lambda k Qv).width := by
  rw [width_spec]
  rw [←(power_data (25+k)).1]
  exact GeneralPaperPowerCeiling.ceiling_lower _

theorem width_lower (m lambda k Qv : ℕ) : 4*((parameters m lambda k Qv).height+1)≤(parameters m lambda k Qv).width := by
  have hp : 1≤2^(25+k) := by have := Nat.two_pow_pos (25+k); omega
  have he := Nat.mul_le_mul_left (4*((parameters m lambda k Qv).height+1)) hp
  simp only [Nat.mul_one] at he
  exact he.trans (width_target_lower m lambda k Qv)

theorem width_target_upper (m lambda k Qv : ℕ) :
    (parameters m lambda k Qv).width<2*(4*((parameters m lambda k Qv).height+1)*2^(25+k)) := by
  rw [width_spec,←(power_data (25+k)).1]
  exact GeneralPaperPowerCeiling.ceiling_upper _ (by
    have he : 0<(powerRun (25+k)).power := by rw [(power_data (25+k)).1]; positivity
    positivity)

theorem width_minimal (m lambda k Qv r : ℕ)
    (hR : 4*((parameters m lambda k Qv).height+1)*2^(25+k)≤2^r) : (parameters m lambda k Qv).width≤2^r := by
  rw [width_spec,GeneralPaperPowerCeiling.ceiling_power]
  apply Nat.pow_le_pow_right (by decide : 1≤2)
  apply GeneralPaperPowerCeiling.ceiling_minimal
  simpa only [(power_data (25+k)).1] using hR

theorem accuracy (m lambda k Qv : ℕ) :
    (4:ℚ)*((parameters m lambda k Qv).height+1:ℕ)≤
      (GeneralPaperSourceParameters.prepare k).eta*(parameters m lambda k Qv).width := by
  have he : (4:ℚ)*((parameters m lambda k Qv).height+1:ℕ)*(2:ℚ)^(25+k)≤(parameters m lambda k Qv).width := by
    exact_mod_cast width_target_lower m lambda k Qv
  rw [(GeneralPaperSourceParameters.data k).2.1,div_mul_eq_mul_div,one_mul]
  exact (le_div_iff₀ (by positivity : (0:ℚ)<(2:ℚ)^(25+k))).mpr he

theorem width_dyadic (m lambda k Qv : ℕ) : ∃ r, (parameters m lambda k Qv).width=2^r := by
  rw [width_spec]
  exact ⟨_,GeneralPaperPowerCeiling.ceiling_power _⟩

theorem exponent_spec (m lambda k Qv : ℕ) : (parameters m lambda k Qv).exponent=
    (GeneralPaperPowerCeiling.ceiling (4*(parameters m lambda k Qv).qProf)).doublings := rfl

theorem exponent_lower (m lambda k Qv : ℕ) : 4*(parameters m lambda k Qv).qProf≤2^(parameters m lambda k Qv).exponent := by
  rw [exponent_spec,←GeneralPaperPowerCeiling.ceiling_power]
  exact GeneralPaperPowerCeiling.ceiling_lower _

theorem exponent_minimal (m lambda k Qv B : ℕ) (hB : 4*(parameters m lambda k Qv).qProf≤2^B) :
    (parameters m lambda k Qv).exponent≤B := by
  rw [exponent_spec]
  exact GeneralPaperPowerCeiling.ceiling_minimal _ B hB

structure Prepared where
  parameters : Parameters
  grid : GeneralPaperProfitGridPrepare.Prepared parameters.qProf parameters.width parameters.exponent

def prepare (m lambda k Qv : ℕ) : Prepared :=
  let p := parameters m lambda k Qv
  ⟨p,GeneralPaperProfitGridPrepare.prepare p.qProf p.width p.exponent⟩

def solve {K : ℕ} (prepared : Prepared) (tree : GeneralPaperBalancedProfitDP.Tree K prepared.parameters.height) (budget : ℚ) :
    Option (Fin prepared.grid.size × List (Fin K)) := GeneralPaperProfitRoot.solve prepared.grid tree budget

end Blotto.GeneralPaperProfitParameters
