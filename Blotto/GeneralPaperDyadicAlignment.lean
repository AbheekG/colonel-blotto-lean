import Blotto.GeneralPaperMantissaQuotient

/-! Ordered addition aligns at most p mantissa bits. A farther positive
summand is discarded with proved relative error, without constructing a huge
shift or rational power from the encoded exponent gap.
-/
namespace Blotto.GeneralPaperDyadicAlignment
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2000000

def gap (high low : Number) : ℕ := (high.exponent-low.exponent).toNat

theorem gap_identity (high low : Number) (hOrder : low.exponent≤high.exponent) :
    high.exponent=low.exponent+(gap high low:ℤ) := by
  unfold gap
  rw [Int.toNat_of_nonneg (by omega)]
  omega

theorem small_summand (unit p : ℕ) (hUnit : 0<unit) (hPower : unit=2^p)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit)
    (hOrder : low.exponent≤high.exponent) (hFar : p<gap high low) :
    (unit:ℚ)*value low≤value high := by
  have hGap := gap_identity high low hOrder
  have hFarZ : (p:ℤ)+1≤gap high low := by exact_mod_cast (show p+1≤gap high low by omega)
  have hExp : (p:ℤ)+1+low.exponent≤high.exponent := by omega
  have hScale : (0:ℚ)<(2:ℚ)^low.exponent := by positivity
  have hm : (low.mantissa:ℚ)<2*(unit:ℚ) := by exact_mod_cast hLow.2
  have hLowBound := mul_lt_mul_of_pos_right hm hScale
  have hUnitPower : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  have hUpper : 2*(unit:ℚ)*(2:ℚ)^low.exponent=(2:ℚ)^((p:ℤ)+1+low.exponent) := by
    rw [zpow_add₀ (by norm_num),zpow_add₀ (by norm_num),zpow_one,zpow_natCast,hUnitPower]
    ring
  rw [hUpper] at hLowBound
  have hMon := zpow_le_zpow_right₀ (by norm_num : (1:ℚ)≤2) hExp
  have hSmall : value low≤(2:ℚ)^high.exponent := hLowBound.le.trans hMon
  have hMantHigh : (unit:ℚ)≤high.mantissa := by exact_mod_cast hHigh.1
  have hHighBound := mul_le_mul_of_nonneg_right hMantHigh (by positivity : (0:ℚ)≤(2:ℚ)^high.exponent)
  exact (mul_le_mul_of_nonneg_left hSmall (by positivity)).trans hHighBound

theorem discard_certificate (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit)
    (hOrder : low.exponent≤high.exponent) (hFar : p<gap high low) :
    retention unit*(value high+value low)≤value high ∧ value high≤value high+value low := by
  have he := small_summand unit p (by omega) hPower high low hHigh hLow hOrder hFar
  have hu : (0:ℚ)<unit := by exact_mod_cast (show 0<unit by omega)
  refine ⟨?_,by linarith [value_nonnegative low]⟩
  unfold retention
  apply (mul_le_mul_iff_right₀ hu).mp
  have hEq : (unit:ℚ)*((1-1/(unit:ℚ))*(value high+value low))=
      ((unit:ℚ)-1)*(value high+value low) := by field_simp
  rw [hEq]
  nlinarith only [he,value_nonnegative low]

def alignedSum (high low : Number) (scale : ℕ) : ℕ := high.mantissa*scale+low.mantissa

def carry (unit input scale : ℕ) : Bool := decide (2*unit*scale≤ input)

def divisor (unit input scale : ℕ) : ℕ := if carry unit input scale then 2*scale else scale

def offset (unit input scale : ℕ) : ℕ := if carry unit input scale then 1 else 0

theorem alignment_bounds (unit scale : ℕ) (hUnit : 0<unit) (hScale : 0<scale)
    (high low : Number) (hHigh : unit≤high.mantissa ∧ high.mantissa<2*unit)
    (hLow : unit≤low.mantissa ∧ low.mantissa<2*unit) :
    0<divisor unit (alignedSum high low scale) scale ∧
      unit*divisor unit (alignedSum high low scale) scale≤alignedSum high low scale ∧
      alignedSum high low scale<2*unit*divisor unit (alignedSum high low scale) scale := by
  have hLowProd := Nat.mul_le_mul_right scale hHigh.1
  have hHighProd := Nat.mul_lt_mul_of_pos_right hHigh.2 hScale
  have hScaleLow : 1≤scale := by omega
  have hSmall := Nat.mul_le_mul_left (2*unit) hScaleLow
  unfold divisor carry
  split
  · rename_i hCarry
    simp only [decide_eq_true_eq] at hCarry
    refine ⟨by omega,by nlinarith,?_⟩
    unfold alignedSum at *
    nlinarith
  · rename_i hCarry
    simp only [decide_eq_true_eq] at hCarry
    refine ⟨hScale,?_,by omega⟩
    unfold alignedSum
    nlinarith

theorem divisor_power (unit input scale degree : ℕ) (hScale : scale=2^degree) :
    divisor unit input scale=2^(degree+offset unit input scale) := by
  unfold divisor offset
  split
  · simp only [pow_succ,hScale]; omega
  · simp only [Nat.add_zero,hScale]

theorem aligned_value (high low : Number) (degree scale : ℕ)
    (hGap : high.exponent=low.exponent+(degree:ℤ)) (hScale : scale=2^degree) :
    value high+value low=(alignedSum high low scale:ℚ)*(2:ℚ)^low.exponent := by
  unfold value alignedSum
  rw [hGap,zpow_add₀ (by norm_num),zpow_natCast,hScale]
  push_cast
  ring

end Blotto.GeneralPaperDyadicAlignment
