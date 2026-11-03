import Blotto.PlayerSpecificAlgebraicTerminalLeafZeros

/-! The actual least sufficient scaled precision uses integer word lengths
and one shifted comparison. Its value depends on the numerical ratio,
not on a supplied precision or on denominator encoding length alone. -/
namespace Blotto.PlayerSpecificRationalPrecision
set_option autoImplicit false
set_option maxHeartbeats 2500000

def exponent (C : ℕ) (epsilon : ℚ) : ℕ := binaryRatioPrecision (C*epsilon.den) epsilon.num.toNat

theorem numerator_bound (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    C*epsilon.den ≤ epsilon.num.toNat*2^exponent C epsilon :=
  binaryRatioPrecision_bound _ _ (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr he))

theorem numerator_cast (epsilon : ℚ) (he : 0 < epsilon) : (epsilon.num.toNat:ℚ)=epsilon*epsilon.den := by
  have hd : (0:ℚ) < epsilon.den := by exact_mod_cast epsilon.den_pos
  rw [ProbabilityWords.nonnegative_numerator_cast epsilon he.le]
  exact (div_eq_iff (ne_of_gt hd)).mp epsilon.num_div_den

theorem guard (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (C:ℚ) ≤ epsilon*(2:ℚ)^exponent C epsilon := by
  have hd : (0:ℚ) < epsilon.den := by exact_mod_cast epsilon.den_pos
  have h : (C:ℚ)*epsilon.den ≤ (epsilon.num.toNat:ℚ)*(2:ℚ)^exponent C epsilon := by
    exact_mod_cast numerator_bound C epsilon he
  rw [numerator_cast epsilon he] at h
  apply (mul_le_mul_iff_of_pos_right hd).mp
  convert! h using 1; ring

theorem minimal (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) (K : ℕ)
    (hK : (C:ℚ) ≤ epsilon*(2:ℚ)^K) : exponent C epsilon ≤ K := by
  have hd : (0:ℚ) < epsilon.den := by exact_mod_cast epsilon.den_pos
  have h : (C:ℚ)*epsilon.den ≤ (epsilon.num.toNat:ℚ)*(2:ℚ)^K := by
    rw [numerator_cast epsilon he]
    convert! mul_le_mul_of_nonneg_right hK hd.le using 1; ring
  have hn : C*epsilon.den ≤ epsilon.num.toNat*2^K := by exact_mod_cast h
  exact binaryRatioPrecision_minimal _ _ (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr he)) K hn

theorem real_guard (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (C:ℝ) ≤ (epsilon:ℝ)*(2:ℝ)^exponent C epsilon := by exact_mod_cast guard C epsilon he

theorem real_minimal (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) (K : ℕ)
    (hK : (C:ℝ) ≤ (epsilon:ℝ)*(2:ℝ)^K) : exponent C epsilon ≤ K := by
  apply minimal C epsilon he K
  exact_mod_cast hK

theorem inverse_power (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) (hC : 0 < C) :
    1/(2:ℝ)^exponent C epsilon ≤ (epsilon:ℝ)/C := by
  have hp : (0:ℝ) < (2:ℝ)^exponent C epsilon := pow_pos (by norm_num) _
  have hc : (0:ℝ) < C := by exact_mod_cast hC
  exact (div_le_div_iff₀ hp hc).mpr (by simpa using real_guard C epsilon he)

theorem scale_bound (C : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    exponent C epsilon ≤ exponent 1 epsilon+binaryWordWidth C := by
  apply binaryRatioPrecision_minimal _ _ (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr he))
  have hb := numerator_bound 1 epsilon he
  simp only [one_mul] at hb
  have hc : C ≤ 2^binaryWordWidth C := (lt_pow_binaryWordWidth C).le
  have h := Nat.mul_le_mul hc hb
  simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using h

end Blotto.PlayerSpecificRationalPrecision
