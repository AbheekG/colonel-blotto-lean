import Blotto.SignificandExponentBounds

/-! A conservative finite rational Taylor lower backend for exp(-x), x≤1/4.
It subtracts a proved absolute remainder envelope from the partial sum, then
uses the actual dyadic rounder. This is a checked alternative to the retained
adaptive odd-term loop; its term count is explicit and logarithmic in tolerance. -/

namespace Blotto
open scoped BigOperators
namespace SparseMW

def expPartial (x : ℚ) (terms : ℕ) : ℚ :=
  ∑ i ∈ Finset.range terms, (-x) ^ i / (Nat.factorial i : ℚ)

def expRemainder (terms : ℕ) : ℚ := 2 / (4 : ℚ) ^ terms

def expLowerTaylor (x : ℚ) (terms : ℕ) : ℚ := expPartial x terms - expRemainder terms

theorem expPartial_real (x : ℚ) (terms : ℕ) :
    (expPartial x terms : ℝ) = ∑ i ∈ Finset.range terms, (-(x : ℝ)) ^ i / (Nat.factorial i : ℝ) := by
  unfold expPartial
  push_cast
  rfl

theorem factorial_real_ge_one (terms : ℕ) : (1 : ℝ) ≤ (Nat.factorial terms : ℝ) := by
  exact_mod_cast Nat.factorial_pos terms

theorem expPartial_error (x : ℚ) (hx : 0 ≤ x ∧ x ≤ 1 / 4) (terms : ℕ) (hn : 0 < terms) :
    |Real.exp (-(x : ℝ)) - (expPartial x terms : ℝ)| ≤ (expRemainder terms : ℝ) := by
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx.1
  have hx1 : (x : ℝ) ≤ (1 / 4 : ℝ) := by
    have he : (x : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hx.2
    norm_num at he ⊢
    exact he
  have hxr := And.intro hx0 hx1
  have ha : |-(x : ℝ)| ≤ 1 := by rw [abs_neg, abs_of_nonneg hxr.1]; linarith
  have he := Real.exp_bound ha (n := terms) hn
  rw [← expPartial_real] at he
  have hpow : |-(x : ℝ)| ^ terms ≤ (1 / 4 : ℝ) ^ terms := by
    rw [abs_neg, abs_of_nonneg hxr.1]
    exact pow_le_pow_left₀ hxr.1 hxr.2 terms
  have hFact := factorial_real_ge_one terms
  have hCoef : (Nat.factorial terms : ℝ)⁻¹ * ((terms : ℝ) + 1) / terms ≤ 2 := by
    have ht : (1 : ℝ) ≤ terms := by exact_mod_cast hn
    have hInv : (Nat.factorial terms : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hFact
    have hRatio : ((terms : ℝ) + 1) / terms ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have hProduct := mul_le_mul hInv hRatio (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul, div_eq_mul_inv, mul_assoc] using hProduct
  have hBound : |-(x : ℝ)| ^ terms * (Nat.factorial terms : ℝ)⁻¹ * ((terms : ℝ) + 1) / terms ≤ 2 * (1 / 4 : ℝ) ^ terms := by
    calc
      _ = |-(x : ℝ)| ^ terms * ((Nat.factorial terms : ℝ)⁻¹ * ((terms : ℝ) + 1) / terms) := by ring
      _ ≤ (1 / 4 : ℝ) ^ terms * 2 := mul_le_mul hpow hCoef (by positivity) (by positivity)
      _ = _ := by ring
  unfold expRemainder
  push_cast
  have hEq : (2 : ℝ) * (1 / 4 : ℝ) ^ terms = 2 / (4 : ℝ) ^ terms := by rw [one_div_pow]; ring
  have hRhs : |-(x : ℝ)| ^ terms * ((terms.succ : ℝ) / ((Nat.factorial terms : ℝ) * terms)) =
      |-(x : ℝ)| ^ terms * (Nat.factorial terms : ℝ)⁻¹ * ((terms : ℝ) + 1) / terms := by
    push_cast
    ring
  rw [hRhs] at he
  exact he.trans (hBound.trans_eq hEq)

theorem expLowerTaylor_upper (x : ℚ) (hx : 0 ≤ x ∧ x ≤ 1 / 4) (terms : ℕ) (hn : 0 < terms) :
    (expLowerTaylor x terms : ℝ) ≤ Real.exp (-(x : ℝ)) := by
  have he := (abs_le.mp (expPartial_error x hx terms hn)).1
  unfold expLowerTaylor
  push_cast
  linarith

theorem expLowerTaylor_error (x : ℚ) (hx : 0 ≤ x ∧ x ≤ 1 / 4) (terms : ℕ) (hn : 0 < terms) :
    Real.exp (-(x : ℝ)) - (expLowerTaylor x terms : ℝ) ≤ 2 * (expRemainder terms : ℝ) := by
  have he := (abs_le.mp (expPartial_error x hx terms hn)).2
  unfold expLowerTaylor
  push_cast
  linarith

def expTerms (theta : ℚ) : ℕ := roundingPrecision theta + 2

theorem expTerms_positive (theta : ℚ) : 0 < expTerms theta := by
  unfold expTerms
  omega

theorem expTerms_bound (theta : ℚ) (ht : 0 < theta) :
    expTerms theta ≤ binaryWordWidth theta.den + 2 := by
  exact Nat.add_le_add_right (roundingPrecision_bound theta ht) 2

theorem expTerms_remainder (theta : ℚ) (ht : 0 < theta) :
    2 * expRemainder (expTerms theta) ≤ theta / 4 := by
  have hp := roundingPrecision_guard theta ht
  have hP : (2 : ℚ) ^ roundingPrecision theta ≤ (4 : ℚ) ^ roundingPrecision theta :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hInv : 1 / (4 : ℚ) ^ roundingPrecision theta ≤
      1 / (2 : ℚ) ^ roundingPrecision theta := one_div_le_one_div_of_le (by positivity) hP
  have he := hInv.trans hp
  unfold expRemainder expTerms
  rw [pow_add]
  norm_num
  convert (div_le_div_of_nonneg_right he (by norm_num : (0 : ℚ) ≤ 4)) using 1
  ring

def expApproximation (x theta : ℚ) : ℚ := expLowerTaylor x (expTerms theta)

theorem expApproximation_certificate (x theta : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    (1 / 2 : ℚ) ≤ expApproximation x theta ∧
    (expApproximation x theta : ℝ) ≤ Real.exp (-(x : ℝ)) ∧
    Real.exp (-(x : ℝ)) - (expApproximation x theta : ℝ) ≤ (theta : ℝ) / 4 := by
  have hUpper := expLowerTaylor_upper x hx (expTerms theta) (expTerms_positive theta)
  have hError := expLowerTaylor_error x hx (expTerms theta) (expTerms_positive theta)
  have hRem : 2 * (expRemainder (expTerms theta) : ℝ) ≤ (theta : ℝ) / 4 := by
    exact_mod_cast expTerms_remainder theta ht.1
  have hError' := hError.trans hRem
  have hxR : (x : ℝ) ≤ (1 / 4 : ℝ) := by
    have he : (x : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hx.2
    norm_num at he
    exact he
  have htR : (theta : ℝ) ≤ (1 / 2 : ℝ) := by
    have he : (theta : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr ht.2
    norm_num at he
    exact he
  have he := Real.add_one_le_exp (-(x : ℝ))
  have hPositive : (1 / 2 : ℝ) ≤ (expLowerTaylor x (expTerms theta) : ℝ) := by linarith
  refine ⟨?_, hUpper, hError'⟩
  change (1 / 2 : ℚ) ≤ expLowerTaylor x (expTerms theta)
  have he : (((1 / 2 : ℚ) : ℝ)) ≤ (expLowerTaylor x (expTerms theta) : ℝ) := by
    norm_num
    exact hPositive
  exact Rat.cast_le.mp he

theorem expApproximation_exp_lower (x theta : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    Real.exp (-(x : ℝ) - (theta : ℝ)) ≤ (expApproximation x theta : ℝ) := by
  have hc := expApproximation_certificate x theta hx ht
  have hPos : (1 / 2 : ℝ) ≤ (expApproximation x theta : ℝ) := by
    have he : ((1 / 2 : ℚ) : ℝ) ≤ (expApproximation x theta : ℝ) := Rat.cast_le.mpr hc.1
    norm_num at he
    exact he
  have ht0 : (0 : ℝ) ≤ (theta : ℝ) := by exact_mod_cast ht.1.le
  have hProduct : Real.exp (-(x : ℝ)) ≤
      (1 + (theta : ℝ)) * (expApproximation x theta : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hPos ht0
    nlinarith [hc.2.2]
  have hexp : 1 + (theta : ℝ) ≤ Real.exp (theta : ℝ) := by
    simpa only [add_comm] using Real.add_one_le_exp (theta : ℝ)
  have hMul := mul_le_mul_of_nonneg_left
    (hProduct.trans (mul_le_mul_of_nonneg_right hexp (by linarith : (0 : ℝ) ≤ (expApproximation x theta : ℝ))))
    (Real.exp_pos (-(theta : ℝ))).le
  have hCancel : Real.exp (-(theta : ℝ)) * Real.exp (theta : ℝ) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [← mul_assoc, hCancel, one_mul, ← Real.exp_add] at hMul
  have harg : -(theta : ℝ) + -(x : ℝ) = -(x : ℝ) - (theta : ℝ) := by ring
  rw [harg] at hMul
  exact hMul

def expMultiplier (x theta : ℚ) : ℚ := roundToTolerance (expApproximation x theta) theta

theorem expMultiplier_certificate (x theta : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 < expMultiplier x theta ∧
    Real.exp (-(x : ℝ) - 2 * (theta : ℝ)) ≤ (expMultiplier x theta : ℝ) ∧
    (expMultiplier x theta : ℝ) ≤ Real.exp (-(x : ℝ)) := by
  have ha := expApproximation_certificate x theta hx ht
  have hap : 0 < expApproximation x theta := by linarith [ha.1]
  have hr := roundToTolerance_certificate (expApproximation x theta) theta hap ht.1
  have hl := roundToTolerance_exp_lower (expApproximation x theta) theta hap ht.1
  have he := expApproximation_exp_lower x theta hx ht
  refine ⟨hr.1, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-(theta : ℝ))).le
    have hc := hm.trans hl
    rw [← Real.exp_add] at hc
    have harg : -(theta : ℝ) + (-(x : ℝ) - (theta : ℝ)) = -(x : ℝ) - 2 * (theta : ℝ) := by ring
    rw [harg] at hc
    exact hc
  · have hh : (roundToTolerance (expApproximation x theta) theta : ℝ) ≤
        (expApproximation x theta : ℝ) := by exact_mod_cast hr.2.1
    exact hh.trans ha.2.1

theorem expMultiplier_effectiveLoss (eta loss theta : ℚ)
    (heta : 0 < eta) (hx : 0 ≤ eta * loss ∧ eta * loss ≤ 1 / 4)
    (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    (loss : ℝ) ≤ effectiveLoss (eta : ℝ) (expMultiplier (eta * loss) theta : ℝ) ∧
    effectiveLoss (eta : ℝ) (expMultiplier (eta * loss) theta : ℝ) ≤
      (loss : ℝ) + 2 * (theta : ℝ) / (eta : ℝ) := by
  have hc := expMultiplier_certificate (eta * loss) theta hx ht
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta
  apply effectiveLoss_error hetaR
  · simpa only [Rat.cast_mul, neg_mul] using hc.2.1
  · simpa only [Rat.cast_mul, neg_mul] using hc.2.2

/-- Returns the partial sum and the next Taylor term in one rational recurrence. -/
def expSeriesState (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1)
  | terms + 1 =>
      let state := expSeriesState x terms
      (state.1 + state.2, state.2 * (-x) / (terms + 1))

theorem expSeriesState_refines (x : ℚ) (terms : ℕ) :
    expSeriesState x terms =
      (expPartial x terms, (-x) ^ terms / (Nat.factorial terms : ℚ)) := by
  induction terms with
  | zero => simp [expSeriesState, expPartial]
  | succ terms ih =>
    rw [expSeriesState, ih]
    apply Prod.ext
    · simp [expPartial, Finset.sum_range_succ]
    · change (-x) ^ terms / (Nat.factorial terms : ℚ) * (-x) / (terms + 1) =
        (-x) ^ (terms + 1) / (Nat.factorial (terms + 1) : ℚ)
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      have hf : (Nat.factorial terms : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero terms
      have hn : (terms : ℚ) + 1 ≠ 0 := by positivity
      field_simp

def expLowerNative (x theta : ℚ) : ℚ :=
  (expSeriesState x (expTerms theta)).1 - expRemainder (expTerms theta)

theorem expLowerNative_refines (x theta : ℚ) :
    expLowerNative x theta = expApproximation x theta := by
  simp [expLowerNative, expSeriesState_refines, expApproximation, expLowerTaylor]

def expMultiplierNative (x theta : ℚ) : ℚ := roundToTolerance (expLowerNative x theta) theta

theorem expMultiplierNative_refines (x theta : ℚ) :
    expMultiplierNative x theta = expMultiplier x theta := by
  rw [expMultiplierNative, expLowerNative_refines]
  rfl

theorem expMultiplierNative_certificate (x theta : ℚ)
    (hx : 0 ≤ x ∧ x ≤ 1 / 4) (ht : 0 < theta ∧ theta ≤ 1 / 2) :
    0 < expMultiplierNative x theta ∧
    Real.exp (-(x : ℝ) - 2 * (theta : ℝ)) ≤ (expMultiplierNative x theta : ℝ) ∧
    (expMultiplierNative x theta : ℝ) ≤ Real.exp (-(x : ℝ)) := by
  rw [expMultiplierNative_refines]
  exact expMultiplier_certificate x theta hx ht

end SparseMW
end Blotto
