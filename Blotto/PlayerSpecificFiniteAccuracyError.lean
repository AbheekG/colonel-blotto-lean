import Blotto.PlayerSpecificAlgebraicOutputFloorSpecification

/-! The three actual computed precisions meet the paper's numerical
error ledger. This is the numerical bound; whole-law and CDF joins are
separate obligations and are not inferred from this calculation. -/
namespace Blotto.PlayerSpecificFiniteAccuracyError
open PlayerSpecificFiniteAccuracy PlayerSpecificRationalPrecision
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem shifted_grid (s R : ℕ) : (1/(2:ℝ)^(s+R))/(1/(2:ℝ)^s)=1/(2:ℝ)^R := by
  rw [pow_add]
  field_simp

theorem scalar_error (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    3/(2*(2:ℝ)^(prepare N s epsilon).scalarBits) ≤ (epsilon:ℝ)/32 := by
  have h := inverse_power 48 epsilon he (by decide)
  change 1/(2:ℝ)^(prepare N s epsilon).scalarBits ≤ (epsilon:ℝ)/48 at h
  have hm := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 3/2)
  convert! hm using 1 <;> ring

theorem coin_error (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (N+1000:ℝ)/(2:ℝ)^(prepare N s epsilon).coinBits ≤ (epsilon:ℝ)/32 := by
  have h := inverse_power (32*(N+1000)) epsilon he (by omega)
  change 1/(2:ℝ)^(prepare N s epsilon).coinBits ≤ (epsilon:ℝ)/(32*(N+1000):ℕ) at h
  have hm := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ N+1000)
  have hn : (N+1000:ℝ) ≠ 0 := by positivity
  have hr : (N+1000:ℝ)*((epsilon:ℝ)/(32*(N+1000):ℕ))=(epsilon:ℝ)/32 := by
    push_cast
    field_simp
  rw [hr] at hm
  simpa only [mul_one_div] using hm

theorem output_error (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (1/(2:ℝ)^(prepare N s epsilon).outputBits)/(1/(2:ℝ)^s) ≤ (epsilon:ℝ)/32 := by
  change (1/(2:ℝ)^(s+exponent 32 epsilon))/(1/(2:ℝ)^s) ≤ _
  rw [shifted_grid]
  exact inverse_power 32 epsilon he (by decide)

theorem total_error (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    3/(2*(2:ℝ)^(prepare N s epsilon).scalarBits)+(N+1000:ℝ)/(2:ℝ)^(prepare N s epsilon).coinBits+
      (1/(2:ℝ)^(prepare N s epsilon).outputBits)/(1/(2:ℝ)^s) ≤ 3*(epsilon:ℝ)/32 := by
  linarith only [scalar_error N s epsilon he,coin_error N s epsilon he,output_error N s epsilon he]

theorem regret_allowance (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    3*(3/(2*(2:ℝ)^(prepare N s epsilon).scalarBits)+(N+1000:ℝ)/(2:ℝ)^(prepare N s epsilon).coinBits+
      (1/(2:ℝ)^(prepare N s epsilon).outputBits)/(1/(2:ℝ)^s)) < (epsilon:ℝ) := by
  have hr : (0:ℝ) < epsilon := by exact_mod_cast he
  linarith only [total_error N s epsilon he,hr]

end Blotto.PlayerSpecificFiniteAccuracyError
