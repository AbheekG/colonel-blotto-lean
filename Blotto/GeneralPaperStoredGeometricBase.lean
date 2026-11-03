import Blotto.GeneralPaperPowerPrecision

/-! Exact dyadic base construction at the selected precision. Both powers
used to construct the mantissa are produced by doubling; the signed exponent
is stored. The base decrement is 2^(-(55+2*k)).
-/
namespace Blotto.GeneralPaperStoredGeometricBase
open GeneralPaperDyadicFloat GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000

def decrementBits (k : ℕ) : ℕ := 55+2*k

def construct (unit p k : ℕ) : GeneralPaperDyadicMultiply.Result :=
  let quantum := powerRun (p+1-decrementBits k)
  ⟨⟨2*unit-quantum.power,-((p+1:ℕ):ℤ)⟩,quantum.work+16⟩

theorem quantum_bound (unit p k : ℕ) (hPower : unit=2^p) :
    (powerRun (p+1-decrementBits k)).power≤unit := by
  rw [(power_data _).1,hPower]
  apply Nat.pow_le_pow_right (by decide : 1≤2)
  unfold decrementBits
  omega

theorem construct_normal (unit p k : ℕ) (hUnit : 0<unit) (hPower : unit=2^p) :
    Normal unit (construct unit p k).number ∧ 0<(construct unit p k).number.mantissa := by
  have hq := quantum_bound unit p k hPower
  have hp : 0<(powerRun (p+1-decrementBits k)).power := by rw [(power_data _).1]; positivity
  exact ⟨Or.inr ⟨by change unit≤2*unit-(powerRun _).power; omega,
    by change 2*unit-(powerRun _).power<2*unit; omega⟩,
    by change 0<2*unit-(powerRun _).power; omega⟩

theorem decrement_formula (k : ℕ) :
    GeneralPaperGeometricLevels.geometricBase (GeneralPaperSourceParameters.prepare k).eta
      (GeneralPaperSourceParameters.prepare k).theta=1-1/(2:ℚ)^decrementBits k := by
  unfold GeneralPaperGeometricLevels.geometricBase decrementBits
  rw [(GeneralPaperSourceParameters.data k).2.1,(GeneralPaperSourceParameters.data k).2.2.2.1]
  rw [show 55+2*k=((25+k)+(29+k))+1 by omega,pow_succ,pow_add]
  field_simp
  <;> ring

theorem construct_value (unit p k : ℕ) (hPower : unit=2^p) (hPrecision : decrementBits k≤p+1) :
    value (construct unit p k).number=1-1/(2:ℚ)^decrementBits k := by
  have hq := quantum_bound unit p k hPower
  have hSub : (powerRun (p+1-decrementBits k)).power≤2*unit := by omega
  have hIdentity : (2:ℚ)^(p+1-decrementBits k)*(2:ℚ)^decrementBits k=(2:ℚ)^(p+1) := by
    rw [← pow_add,Nat.sub_add_cancel hPrecision]
  unfold construct value
  dsimp only
  rw [Nat.cast_sub hSub,(power_data _).1]
  rw [zpow_neg,zpow_natCast]
  push_cast
  have hPowerQ : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  rw [hPowerQ]
  field_simp
  rw [pow_succ] at hIdentity ⊢
  nlinarith only [hIdentity]

theorem selected_value (lambda k : ℕ) :
    value (construct (GeneralPaperPowerPrecision.prepare lambda k).unit
      (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits k).number=
      GeneralPaperGeometricLevels.geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta := by
  rw [construct_value _ _ k (GeneralPaperPowerPrecision.unit_power lambda k),decrement_formula]
  have hp := GeneralPaperPowerPrecision.bits_minimum lambda k
  unfold decrementBits
  omega

theorem construct_work (unit p k : ℕ) : (construct unit p k).work=8*(p+1-decrementBits k)+18 := by
  unfold construct
  dsimp only
  rw [(power_data _).2.2]

end Blotto.GeneralPaperStoredGeometricBase
