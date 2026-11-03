import Blotto.GeneralPaperPowerQueryExponent

/-! Convert the checked downward mass certificate into an encoded signed
exponent bound. Rational powers here are reference semantics only; no stored
arithmetic or query expands its encoded exponent into a rational power.
-/
namespace Blotto.GeneralPaperMassExponentRange
open GeneralPaperDyadicFloat GeneralPaperCenteredExponent GeneralPaperMassApproximation
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem value_bounds (unit p : ℕ) (hPower : unit=2^p) (x : Number) (hNormal : Normal unit x)
    (hPositive : 0<x.mantissa) :
    (2:ℚ)^centered p x≤value x ∧ value x<(2:ℚ)^(centered p x+1) := by
  have hn := hNormal.resolve_left (by intro h; omega)
  have hUnit : (unit:ℚ)=(2:ℚ)^p := by exact_mod_cast hPower
  have hLower : (unit:ℚ)≤x.mantissa := by exact_mod_cast hn.1
  have hUpper : (x.mantissa:ℚ)<2*unit := by exact_mod_cast hn.2
  have hCenter : (2:ℚ)^centered p x=(unit:ℚ)*(2:ℚ)^x.exponent := by
    unfold centered
    rw [zpow_add₀ (by norm_num),zpow_natCast,←hUnit]
    ring
  have hNext : (2:ℚ)^(centered p x+1)=(2*(unit:ℚ))*(2:ℚ)^x.exponent := by
    rw [zpow_add₀ (by norm_num),zpow_one,hCenter]
    ring
  rw [hCenter,hNext]
  exact ⟨mul_le_mul_of_nonneg_right hLower (by positivity),mul_lt_mul_of_pos_right hUpper (by positivity)⟩

theorem centered_bounds (unit p G height : ℕ) (hPower : unit=2^p) (x : Number)
    (hNormal : Normal unit x) (hPositive : 0<x.mantissa)
    (hLower : (2:ℚ)^(-(G:ℤ)-1)≤value x) (hUpper : value x≤(2:ℚ)^(height:ℤ)) :
    -(G:ℤ)-1≤centered p x ∧ centered p x≤height := by
  have hv := value_bounds unit p hPower x hNormal hPositive
  have hl := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℚ)<2)).mp (hLower.trans_lt hv.2)
  have hu := (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℚ)<2)).mp (hv.1.trans hUpper)
  constructor <;> omega

theorem zero_exponent (unit : ℕ) (x : Number) (hNormal : Normal unit x) (hValue : value x=0) : x.exponent=0 := by
  have hz := (value_zero_iff x).mp hValue
  rcases hNormal with h|h
  · exact h.2
  · have hMantissa : (0:ℚ)<(2:ℚ)^x.exponent := by positivity
    have hUnit : unit=0 := by omega
    rw [hUnit] at h
    omega

theorem relative_half (k : ℕ) : (1/2:ℚ)≤1-(GeneralPaperSourceParameters.prepare k).nu/64 := by
  have hEta := GeneralPaperSourceParameters.eta_upper k
  have hNu := GeneralPaperSourceParameters.nu_eta k
  rw [hNu]
  linarith

theorem stored (lambda k exponent G height : ℕ) (exactMass : ℚ) (x : Number)
    (hExponent : exponent≤budget lambda k)
    (h : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit exponent exactMass x)
    (hMass : exactMass=0 ∨ (2:ℚ)^(-(G:ℤ))≤exactMass)
    (hUpper : exactMass≤(2:ℚ)^height) :
    x.exponent.natAbs≤G+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+height+2 := by
  rcases hMass with hZero|hPositive
  · have hz : value x=0 := by have hh:=h.2.2.2; rw [hZero] at hh; exact le_antisymm hh (value_nonnegative x)
    rw [zero_exponent _ x h.1 hz]
    simp only [Int.natAbs_zero,Nat.zero_le]
  · have hRel := selected_relative lambda k exponent exactMass x hExponent h
    have hHalf := relative_half k
    have hExact : 0<exactMass := (by positivity : (0:ℚ)<(2:ℚ)^(-(G:ℤ))).trans_le hPositive
    have hScale := mul_le_mul hHalf hPositive (by positivity) (by linarith)
    have hL : (2:ℚ)^(-(G:ℤ)-1)≤value x := by
      have hIdentity : (1/2:ℚ)*(2:ℚ)^(-(G:ℤ))=(2:ℚ)^(-(G:ℤ)-1) := by
        rw [sub_eq_add_neg,zpow_add₀ (by norm_num),zpow_neg_one]
        ring
      rw [hIdentity] at hScale
      exact hScale.trans hRel.1
    have hPos : 0<x.mantissa := by
      have hv : 0<value x := (by positivity : (0:ℚ)<(2:ℚ)^(-(G:ℤ)-1)).trans_le hL
      have hn : ¬x.mantissa=0 := by intro hz; rw [(value_zero_iff x).mpr hz] at hv; exact (lt_irrefl _ hv)
      omega
    have hU : value x≤(2:ℚ)^(height:ℤ) := by rw [zpow_natCast]; exact hRel.2.trans hUpper
    have hc := centered_bounds _ _ G height (GeneralPaperPowerPrecision.unit_power lambda k) x h.1 hPos hL hU
    unfold centered at hc
    omega

theorem paper_range (lambda k exponent G height : ℕ) (exactMass : ℚ) (x : Number)
    (hHeight : height≤lambda+1) (hExponent : exponent≤budget lambda k)
    (h : Bound (GeneralPaperPreparedPowers.prepare lambda k).format.unit exponent exactMass x)
    (hMass : exactMass=0 ∨ (2:ℚ)^(-(G:ℤ))≤exactMass) (hUpper : exactMass≤(2:ℚ)^height) :
    x.exponent.natAbs≤lambda+G+(GeneralPaperPowerPrecision.prepare lambda k).fractionalBits+8 := by
  have hs := stored lambda k exponent G height exactMass x hExponent h hMass hUpper
  omega

end Blotto.GeneralPaperMassExponentRange
