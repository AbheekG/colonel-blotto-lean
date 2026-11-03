import Blotto.GeneralPaperPreparedPowers

/-! Conversion of local epoch powers to integer numerators over the common
denominator 2^(p+1). Values in [1/2,1] use one of two adjacent stored exponents;
conversion therefore only compares the exponent and possibly doubles the
mantissa. Exact one uses numerator 2^(p+1), with its extra endpoint bit.
-/
namespace Blotto.GeneralPaperLocalPowerNumerators
open scoped BigOperators Classical
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2000000

def numerator (unit p : ℕ) (x : Number) : ℕ :=
  if x.exponent=-(p:ℤ) then 2*x.mantissa else x.mantissa

theorem exponent_bracket (unit p : ℕ) (hPower : unit=2^p) (x : Number)
    (hNormal : Normal unit x) (hLow : (1/2:ℚ)≤value x) (hHigh : value x≤1) :
    -((p+1:ℕ):ℤ)≤x.exponent ∧ x.exponent≤-(p:ℤ) := by
  have hx : 0<x.mantissa := by
    by_contra hn
    have hz : x.mantissa=0 := by omega
    have he : value x=0 := (value_zero_iff x).mpr hz
    rw [he] at hLow
    norm_num at hLow
  have hm := hNormal.resolve_left (by intro h; omega)
  have hScale : (0:ℚ)<(2:ℚ)^x.exponent := by positivity
  have hUnitPower : (unit:ℚ)*(2:ℚ)^x.exponent=(2:ℚ)^((p:ℤ)+x.exponent) := by
    rw [zpow_add₀ (by norm_num),zpow_natCast]
    rw [hPower,Nat.cast_pow,Nat.cast_ofNat]
  have hMantLow : (unit:ℚ)≤x.mantissa := by exact_mod_cast hm.1
  have hMantHigh : (x.mantissa:ℚ)<2*(unit:ℚ) := by exact_mod_cast hm.2
  have hLower := mul_le_mul_of_nonneg_right hMantLow hScale.le
  have hUpper := mul_lt_mul_of_pos_right hMantHigh hScale
  have hTop : (2:ℚ)^((p:ℤ)+x.exponent)≤1 := by
    rw [← hUnitPower]
    exact hLower.trans hHigh
  have hExpTop := (zpow_le_one_iff_right₀ (by norm_num : (1:ℚ)<2)).mp hTop
  have hBottom : (2:ℚ)^(-1:ℤ)<(2:ℚ)^((p:ℤ)+x.exponent+1) := by
    have hEq : (2:ℚ)^((p:ℤ)+x.exponent+1)=2*((unit:ℚ)*(2:ℚ)^x.exponent) := by
      rw [zpow_add₀ (by norm_num),zpow_one,← hUnitPower]
      ring
    rw [hEq]
    norm_num
    dsimp only [value] at hLow
    nlinarith only [hLow,hUpper]
  have hExpBottom := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ)<2)).mp hBottom
  push_cast
  constructor <;> omega

theorem numerator_value (unit p : ℕ) (hPower : unit=2^p) (x : Number)
    (hNormal : Normal unit x) (hLow : (1/2:ℚ)≤value x) (hHigh : value x≤1) :
    value x=(numerator unit p x:ℚ)/(2*(unit:ℚ)) := by
  have he := exponent_bracket unit p hPower x hNormal hLow hHigh
  have hu : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  unfold numerator value
  split
  · rename_i hExp
    rw [hExp,zpow_neg,zpow_natCast]
    push_cast
    rw [hu]
    field_simp
  · rename_i hExp
    have hExact : x.exponent=-((p+1:ℕ):ℤ) := by push_cast at he ⊢; omega
    rw [hExact,zpow_neg,zpow_natCast,hu,pow_succ]
    ring

theorem numerator_bounds (unit p : ℕ) (hPower : unit=2^p) (x : Number)
    (hNormal : Normal unit x) (hLow : (1/2:ℚ)≤value x) (hHigh : value x≤1) :
    unit≤numerator unit p x ∧ numerator unit p x≤2*unit := by
  have hv := numerator_value unit p hPower x hNormal hLow hHigh
  have hu : (0:ℚ)<unit := by rw [hPower,Nat.cast_pow,Nat.cast_ofNat]; positivity
  rw [hv] at hLow hHigh
  have h1 := (le_div_iff₀ (show (0:ℚ)<2*(unit:ℚ) by positivity)).mp hLow
  have h2 := (div_le_iff₀ (show (0:ℚ)<2*(unit:ℚ) by positivity)).mp hHigh
  constructor
  · have he : (unit:ℚ)≤numerator unit p x := by linarith only [h1]
    exact_mod_cast he
  · have he : (numerator unit p x:ℚ)≤2*(unit:ℚ) := by linarith only [h2]
    exact_mod_cast he

theorem one_numerator (unit p : ℕ) : numerator unit p (one unit p)=2*unit := by simp [numerator,one]

theorem normalized_sum {s : ℕ} (location : Fin s → ℕ) (number : Fin s → Number) (unit p : ℕ)
    (hPower : unit=2^p) (hNormal : ∀ r, Normal unit (number r))
    (hLow : ∀ r, (1/2:ℚ)≤value (number r)) (hHigh : ∀ r, value (number r)≤1) (count : ℕ) :
    GeneralPaperSummaryOccurrences.occurrencePrefix location (fun r => (value (number r):ℝ)) count/
      (∑ r, (value (number r):ℝ))=
      ((∑ r, if location r<count then numerator unit p (number r) else 0:ℕ):ℝ)/
        ((∑ r, numerator unit p (number r):ℕ):ℝ) := by
  have hu : (0:ℝ)<unit := by rw [hPower,Nat.cast_pow,Nat.cast_ofNat]; positivity
  have hValue : ∀ r, (value (number r):ℝ)=(numerator unit p (number r):ℝ)/(2*(unit:ℝ)) := by
    intro r
    have he := congrArg (fun q : ℚ => (q:ℝ)) (numerator_value unit p hPower (number r) (hNormal r) (hLow r) (hHigh r))
    push_cast at he
    exact he
  have hTotal : (∑ r, (value (number r):ℝ))=(∑ r, (numerator unit p (number r):ℝ))/(2*(unit:ℝ)) := by
    simp only [hValue,div_eq_mul_inv,Finset.sum_mul]
  have hPrefix : GeneralPaperSummaryOccurrences.occurrencePrefix location (fun r => (value (number r):ℝ)) count=
      (∑ r, if location r<count then (numerator unit p (number r):ℝ) else 0)/(2*(unit:ℝ)) := by
    unfold GeneralPaperSummaryOccurrences.occurrencePrefix
    simp only [hValue]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    split <;> simp
  rw [hPrefix,hTotal]
  push_cast
  exact div_div_div_cancel_right₀ (by positivity : (2*(unit:ℝ))≠0) _ _

end Blotto.GeneralPaperLocalPowerNumerators
