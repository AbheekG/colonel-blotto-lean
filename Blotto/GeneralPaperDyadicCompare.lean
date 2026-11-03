import Blotto.GeneralPaperIntervalMass

/-! Exact comparison of bounded mantissas with encoded exponents. A large
gap is resolved by the exponent order; a small gap constructs at most width
shift bits by doubling. Scaled comparisons support j*total <= s*prefix
without expanding either dyadic value or rounding the comparison target.
-/
namespace Blotto.GeneralPaperDyadicCompare
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  answer : Bool
  work : ℕ

def le (width : ℕ) (left right : Number) : Result :=
  if left.mantissa=0 then ⟨true,8⟩ else
    if right.mantissa=0 then ⟨false,8⟩ else
      if left.exponent≤right.exponent then
        let gap := (right.exponent-left.exponent).toNat
        if width≤gap then ⟨true,16⟩ else
          let shift := GeneralPaperScoreScaleParameters.powerRun gap
          ⟨decide (left.mantissa≤right.mantissa*shift.power),shift.work+24⟩
      else
        let gap := (left.exponent-right.exponent).toNat
        if width≤gap then ⟨false,16⟩ else
          let shift := GeneralPaperScoreScaleParameters.powerRun gap
          ⟨decide (left.mantissa*shift.power≤right.mantissa),shift.work+24⟩

def scale (factor : ℕ) (x : Number) : Number := ⟨factor*x.mantissa,x.exponent⟩

def scaledLE (width leftFactor : ℕ) (left : Number) (rightFactor : ℕ) (right : Number) : Result :=
  let result := le width (scale leftFactor left) (scale rightFactor right)
  ⟨result.answer,result.work+16⟩

theorem scale_value (factor : ℕ) (x : Number) : value (scale factor x)=(factor:ℚ)*value x := by
  unfold scale value
  push_cast
  ring

theorem separated (width : ℕ) (low high : Number) (hLow : low.mantissa<2^width) (hHigh : 0<high.mantissa)
    (hGap : low.exponent+(width:ℤ)≤high.exponent) : value low<value high := by
  have hm : (low.mantissa:ℚ)<(2:ℚ)^width := by exact_mod_cast hLow
  have hPos : (1:ℚ)≤high.mantissa := by exact_mod_cast (show 1≤high.mantissa by omega)
  have hScale : (0:ℚ)<(2:ℚ)^low.exponent := by positivity
  have hLowBound := mul_lt_mul_of_pos_right hm hScale
  have hIdentity : (2:ℚ)^width*(2:ℚ)^low.exponent=(2:ℚ)^(low.exponent+(width:ℤ)) := by
    rw [zpow_add₀ (by norm_num),zpow_natCast]
    ring
  rw [hIdentity] at hLowBound
  have hMon := zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) hGap
  have hHighBound := mul_le_mul_of_nonneg_right hPos (by positivity : (0:ℚ)≤(2:ℚ)^high.exponent)
  simp only [one_mul] at hHighBound
  exact hLowBound.trans_le (hMon.trans hHighBound)

theorem aligned_iff (low high : Number) (hOrder : low.exponent≤high.exponent) :
    value low≤value high ↔ low.mantissa≤high.mantissa*2^(high.exponent-low.exponent).toNat := by
  have hExp : high.exponent=low.exponent+((high.exponent-low.exponent).toNat:ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  unfold value
  rw [hExp,zpow_add₀ (by norm_num),zpow_natCast]
  have hEq : (high.mantissa:ℚ)*((2:ℚ)^low.exponent*(2:ℚ)^(high.exponent-low.exponent).toNat)=
    ((high.mantissa:ℚ)*(2:ℚ)^(high.exponent-low.exponent).toNat)*(2:ℚ)^low.exponent := by ring
  rw [hEq]
  rw [mul_le_mul_iff_left₀ (by positivity : (0:ℚ)<(2:ℚ)^low.exponent)]
  norm_cast
  simp [max_eq_left (by omega : (0:ℤ)≤high.exponent-low.exponent)]

theorem aligned_reverse_iff (low high : Number) (hOrder : low.exponent≤high.exponent) :
    value high≤value low ↔ high.mantissa*2^(high.exponent-low.exponent).toNat≤low.mantissa := by
  have hExp : high.exponent=low.exponent+((high.exponent-low.exponent).toNat:ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]; omega
  unfold value
  rw [hExp,zpow_add₀ (by norm_num),zpow_natCast]
  have hEq : (high.mantissa:ℚ)*((2:ℚ)^low.exponent*(2:ℚ)^(high.exponent-low.exponent).toNat)=
    ((high.mantissa:ℚ)*(2:ℚ)^(high.exponent-low.exponent).toNat)*(2:ℚ)^low.exponent := by ring
  rw [hEq]
  rw [mul_le_mul_iff_left₀ (by positivity : (0:ℚ)<(2:ℚ)^low.exponent)]
  norm_cast
  simp [max_eq_left (by omega : (0:ℤ)≤high.exponent-low.exponent)]

theorem le_correct (width : ℕ) (left right : Number)
    (hLeft : left.mantissa<2^width) (hRight : right.mantissa<2^width) :
    (le width left right).answer=true ↔ value left≤value right := by
  unfold le
  split
  · rename_i hz
    simp only [Bool.true_eq, true_iff]
    rw [(value_zero_iff left).mpr hz]
    exact value_nonnegative right
  · rename_i hL
    split
    · rename_i hz
      have hPos := value_positive left (by omega)
      rw [(value_zero_iff right).mpr hz]
      simp only [Bool.false_eq_true,false_iff]
      linarith
    · rename_i hR
      split
      · rename_i hOrder
        dsimp only
        split
        · rename_i hGap
          have hExp : left.exponent+(width:ℤ)≤right.exponent := by
            have he : (width:ℤ)≤(right.exponent-left.exponent).toNat := by exact_mod_cast hGap
            rw [Int.toNat_of_nonneg (by omega)] at he
            omega
          have hValue := separated width left right hLeft (by omega) hExp
          simp only [true_iff]
          exact hValue.le
        · simp only [(GeneralPaperScoreScaleParameters.power_data _).1,decide_eq_true_eq]
          exact (aligned_iff left right hOrder).symm
      · rename_i hOrder
        dsimp only
        split
        · rename_i hGap
          have hExp : right.exponent+(width:ℤ)≤left.exponent := by
            have he : (width:ℤ)≤(left.exponent-right.exponent).toNat := by exact_mod_cast hGap
            rw [Int.toNat_of_nonneg (by omega)] at he
            omega
          have hValue := separated width right left hRight (by omega) hExp
          simp only [Bool.false_eq_true,false_iff]
          linarith
        · simp only [(GeneralPaperScoreScaleParameters.power_data _).1,decide_eq_true_eq]
          exact (aligned_reverse_iff right left (by omega)).symm

theorem scale_bound (p digits factor : ℕ) (x : Number)
    (hMantissa : x.mantissa<2^(p+1)) (hFactor : factor≤2^digits) :
    (scale factor x).mantissa<2^(p+1+digits) := by
  by_cases hz : factor=0
  · subst factor
    simpa only [scale,Nat.zero_mul] using Nat.two_pow_pos (p+1+digits)
  · have hm := Nat.mul_lt_mul_of_pos_left hMantissa (show 0<factor by omega)
    have hf := Nat.mul_le_mul_right (2^(p+1)) hFactor
    dsimp only [scale]
    rw [pow_add]
    nlinarith

theorem scaled_correct (width leftFactor : ℕ) (left : Number) (rightFactor : ℕ) (right : Number)
    (hLeft : (scale leftFactor left).mantissa<2^width) (hRight : (scale rightFactor right).mantissa<2^width) :
    (scaledLE width leftFactor left rightFactor right).answer=true ↔
      (leftFactor:ℚ)*value left≤(rightFactor:ℚ)*value right := by
  have he := le_correct width (scale leftFactor left) (scale rightFactor right) hLeft hRight
  rw [scale_value,scale_value] at he
  exact he

theorem le_work (width : ℕ) (left right : Number) : (le width left right).work≤8*width+26 := by
  unfold le
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · split <;> dsimp only <;> split
      · dsimp only; omega
      · rename_i hNear
        dsimp only
        rw [(GeneralPaperScoreScaleParameters.power_data _).2.2]
        omega
      · dsimp only; omega
      · rename_i hNear
        dsimp only
        rw [(GeneralPaperScoreScaleParameters.power_data _).2.2]
        omega

theorem scaled_work (width leftFactor : ℕ) (left : Number) (rightFactor : ℕ) (right : Number) :
    (scaledLE width leftFactor left rightFactor right).work≤8*width+42 := by
  have he := le_work width (scale leftFactor left) (scale rightFactor right)
  change (le width (scale leftFactor left) (scale rightFactor right)).work+16≤_
  omega

end Blotto.GeneralPaperDyadicCompare
