import Blotto.GeneralPaperRoundedPowerQuery

/-! Constructed precision and power-table width for the selected source.
Only integer arithmetic, repeated doubling and comparisons are executed.
The returned unit is 2^p and the stored mantissa has p+1 significant bits.
No logarithm, input-encoding length or supplied precision oracle is used.
-/
namespace Blotto.GeneralPaperPowerPrecision
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000

def levelBound (lambda k : ℕ) : ℕ :=
  8*(GeneralPaperTrajectoryParameters.prepare lambda k).rows*(GeneralPaperSourceParameters.prepare k).meshDenominator

def errorFactor (lambda k : ℕ) : ℕ := 16*(levelBound lambda k+1)*(lambda+2)

structure Parameters where
  unit : ℕ
  fractionalBits : ℕ
  columns : ℕ
  work : ℕ

def prepare (lambda k : ℕ) : Parameters :=
  let source := GeneralPaperSourceParameters.prepare k
  let trajectory := GeneralPaperTrajectoryParameters.prepare lambda k
  let G := 8*trajectory.rows*source.meshDenominator
  let E := 16*(G+1)*(lambda+2)
  let nuDen := powerRun (32+k)
  let minimum := powerRun (74+2*k)
  let precision := GeneralPaperPowerCeiling.ceiling (max minimum.power (64*E*nuDen.power))
  let width := GeneralPaperPowerCeiling.ceiling (G+1)
  ⟨precision.power,precision.doublings,width.doublings,
    nuDen.work+minimum.work+precision.work+width.work+source.work+trajectory.work+64⟩

theorem unit_power (lambda k : ℕ) : (prepare lambda k).unit=2^(prepare lambda k).fractionalBits :=
  GeneralPaperPowerCeiling.ceiling_power _

theorem unit_minimum (lambda k : ℕ) : 2^(74+2*k)≤(prepare lambda k).unit := by
  have he := GeneralPaperPowerCeiling.ceiling_lower
    (max (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power))
  have hh := (Nat.le_max_left (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power)).trans he
  simpa only [prepare,errorFactor,levelBound,(power_data (74+2*k)).1,(power_data (32+k)).1] using hh

theorem bits_minimum (lambda k : ℕ) : 74+2*k≤(prepare lambda k).fractionalBits := by
  have he := unit_minimum lambda k
  rw [unit_power] at he
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp he

theorem unit_positive (lambda k : ℕ) : 1<(prepare lambda k).unit := by
  have he := unit_minimum lambda k
  have hp : 2≤2^(74+2*k) := by
    have hh := Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤74+2*k by omega)
    simpa only [pow_one] using hh
  omega

theorem width_cap (lambda k : ℕ) : levelBound lambda k<2^(prepare lambda k).columns := by
  have he := GeneralPaperPowerCeiling.ceiling_lower (levelBound lambda k+1)
  rw [GeneralPaperPowerCeiling.ceiling_power] at he
  change levelBound lambda k<2^(GeneralPaperPowerCeiling.ceiling (levelBound lambda k+1)).doublings
  omega

theorem unit_accuracy (lambda k : ℕ) :
    64*errorFactor lambda k*2^(32+k)≤(prepare lambda k).unit := by
  have he := GeneralPaperPowerCeiling.ceiling_lower
    (max (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power))
  have hh := (Nat.le_max_right (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power)).trans he
  simpa only [prepare,errorFactor,levelBound,(power_data (74+2*k)).1,(power_data (32+k)).1] using hh

theorem factor_lower (lambda k : ℕ) : 16*levelBound lambda k≤errorFactor lambda k := by
  unfold errorFactor
  nlinarith

theorem minimum_redundant (lambda k : ℕ) :
    2^(74+2*k)≤64*errorFactor lambda k*2^(32+k) := by
  have ht := GeneralPaperTrajectoryParameters.rows_positive lambda k
  have hG : 8*(GeneralPaperSourceParameters.prepare k).meshDenominator≤levelBound lambda k := by
    unfold levelBound
    have hm := Nat.mul_le_mul_right (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) (show 1≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows by omega)
    nlinarith only [hm]
  rw [(GeneralPaperSourceParameters.data k).2.2.2.2.1] at hG
  have hE := factor_lower lambda k
  have hLower : 8192*2^(29+k)≤64*errorFactor lambda k := by nlinarith only [hG,hE]
  have hScaled := Nat.mul_le_mul_right (2^(32+k)) hLower
  have hPower : 2^(74+2*k)=8192*2^(29+k)*2^(32+k) := by
    rw [show 74+2*k=(13+(29+k))+(32+k) by omega]
    simp only [pow_add]
    norm_num
  rw [hPower]
  exact hScaled

theorem selected_unit (lambda k : ℕ) : (prepare lambda k).unit=
    (GeneralPaperPowerCeiling.ceiling (64*errorFactor lambda k*2^(32+k))).power := by
  change (GeneralPaperPowerCeiling.ceiling
    (max (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power))).power=_
  rw [(power_data (74+2*k)).1,(power_data (32+k)).1,max_eq_right (minimum_redundant lambda k)]

theorem precision_condition (lambda k : ℕ) :
    (64:ℚ)*errorFactor lambda k/(prepare lambda k).unit≤(GeneralPaperSourceParameters.prepare k).nu := by
  have hu : (0:ℚ)<(prepare lambda k).unit := by exact_mod_cast (show 0<(prepare lambda k).unit by have := unit_positive lambda k; omega)
  have he : (64:ℚ)*(errorFactor lambda k:ℚ)*(2:ℚ)^(32+k)≤(prepare lambda k).unit := by
    exact_mod_cast unit_accuracy lambda k
  rw [(GeneralPaperSourceParameters.data k).2.2.1]
  apply (le_div_iff₀ (by positivity : (0:ℚ)<(2:ℚ)^(32+k))).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hu).mpr
  nlinarith only [he]

theorem local_power_accuracy (lambda k : ℕ) :
    (levelBound lambda k:ℚ)/(prepare lambda k).unit≤(GeneralPaperSourceParameters.prepare k).nu/1024 := by
  have he := precision_condition lambda k
  have hf : (16:ℚ)*levelBound lambda k≤errorFactor lambda k := by exact_mod_cast factor_lower lambda k
  have hu : (0:ℚ)<(prepare lambda k).unit := by exact_mod_cast (show 0<(prepare lambda k).unit by have := unit_positive lambda k; omega)
  have hs := (div_le_iff₀ hu).mp he
  apply (div_le_iff₀ hu).mpr
  nlinarith only [hf,hs]

theorem local_level_bound {n : ℕ} (hn : 0<n) (lambda k count : ℕ)
    (increment : ℕ → Fin n → ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (i : Fin n) : GeneralPaperGeometricLevels.levels increment count i≤levelBound lambda k := by
  have he := GeneralPaperGeometricLevels.levels_bound increment _ count hIncrement i
  have hh := Nat.mul_le_mul_right (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) hCount
  unfold levelBound
  nlinarith only [he,hh]

theorem bits_upper (lambda k : ℕ) : (prepare lambda k).fractionalBits≤
    binaryWordWidth (max (2^(74+2*k)) (64*errorFactor lambda k*2^(32+k))) := by
  have he := GeneralPaperPowerCeiling.loop_depth
    (max (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power)) 1 (by decide)
  simpa only [prepare,errorFactor,levelBound,GeneralPaperPowerCeiling.ceiling,
    (power_data (74+2*k)).1,(power_data (32+k)).1] using he

theorem columns_upper (lambda k : ℕ) : (prepare lambda k).columns≤binaryWordWidth (levelBound lambda k+1) :=
  GeneralPaperPowerCeiling.loop_depth _ 1 (by decide)

theorem prepare_work (lambda k : ℕ) : (prepare lambda k).work≤
    8*(32+k)+8*(74+2*k)+12*binaryWordWidth (max (2^(74+2*k)) (64*errorFactor lambda k*2^(32+k)))+
      12*binaryWordWidth (levelBound lambda k+1)+(GeneralPaperSourceParameters.prepare k).work+
        (GeneralPaperTrajectoryParameters.prepare lambda k).work+72 := by
  have h1 := GeneralPaperPowerCeiling.ceiling_work
    (max (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power))
  have h2 := GeneralPaperPowerCeiling.ceiling_work (levelBound lambda k+1)
  simp only [(power_data (74+2*k)).1,(power_data (32+k)).1] at h1
  change (powerRun (32+k)).work+(powerRun (74+2*k)).work+
    (GeneralPaperPowerCeiling.ceiling (max (powerRun (74+2*k)).power (64*errorFactor lambda k*(powerRun (32+k)).power))).work+
    (GeneralPaperPowerCeiling.ceiling (levelBound lambda k+1)).work+
    (GeneralPaperSourceParameters.prepare k).work+(GeneralPaperTrajectoryParameters.prepare lambda k).work+64≤_
  rw [(power_data (32+k)).2.2,(power_data (74+2*k)).2.2,(power_data (32+k)).1,(power_data (74+2*k)).1]
  omega

end Blotto.GeneralPaperPowerPrecision
