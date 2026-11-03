import Blotto.PlayerSpecificRootMagnitude

/-! Explicit polynomial evaluation bounds and the two-root identity for
degree at most three. These estimates are used with computed rational
Bezout certificates to choose an isolation depth. -/
namespace Blotto.PlayerSpecificEvaluationMagnitude
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude PlayerSpecificSquarefreeAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem horner_bound (p : Data) (U M x : ℝ) (hU : 0≤U) (hM : 0≤M) (hx : |x| ≤ M)
    (h : ∀ q∈p,|(q:ℝ)| ≤ U) :
    |PlayerSpecificSturmVariations.realEvaluate p x| ≤ U*(1+M)^p.length := by
  induction p with
  | nil => simpa only [PlayerSpecificSturmVariations.realEvaluate,List.foldr_nil,List.length_nil,pow_zero,mul_one,abs_zero]
      using hU
  | cons a p ih =>
    have hp := ih (fun q hq => h q (List.mem_cons_of_mem a hq))
    have ha := h a (List.mem_cons_self)
    have ht : (1:ℝ)≤(1+M)^p.length := one_le_pow₀ (by linarith)
    change |(a:ℝ)+x*PlayerSpecificSturmVariations.realEvaluate p x| ≤ U*(1+M)^(p.length+1)
    calc
      _ ≤ |(a:ℝ)| + |x| * |PlayerSpecificSturmVariations.realEvaluate p x| := by
        simpa only [abs_mul] using abs_add_le (a:ℝ) (x*PlayerSpecificSturmVariations.realEvaluate p x)
      _ ≤ U+M*(U*(1+M)^p.length) := add_le_add ha (mul_le_mul hx hp (abs_nonneg _) hM)
      _ ≤ U*(1+M)^(p.length+1) := by rw [pow_succ]; nlinarith only [mul_le_mul_of_nonneg_left ht hU]

theorem encoded_bound (p : Data) (M x : ℝ) (hM : 0≤M) (hx : |x| ≤ M) :
    |(realPolynomial p).eval x| ≤ (2:ℝ)^inputHeight p*(1+M)^p.length := by
  rw [real_evaluate]
  apply horner_bound p _ M x (pow_nonneg (by norm_num) _) hM hx
  intro q hq
  exact (real_upper q _ (member_height p q hq)).le

theorem eval_four (P : Polynomial ℝ) (hP : P.natDegree≤3) (x : ℝ) :
    P.eval x=P.coeff 0+P.coeff 1*x+P.coeff 2*x^2+P.coeff 3*x^3 := by
  rw [Polynomial.eval_eq_sum_range' (show P.natDegree<4 by omega)]
  norm_num [Finset.sum_range_succ]

theorem derivative_four (P : Polynomial ℝ) (hP : P.natDegree≤3) (x : ℝ) :
    P.derivative.eval x=P.coeff 1+2*P.coeff 2*x+3*P.coeff 3*x^2 := by
  have hd : P.derivative.natDegree<4 := lt_of_le_of_lt (Polynomial.natDegree_derivative_le P) (by omega)
  rw [Polynomial.eval_eq_sum_range' hd]
  have h4 : P.coeff 4=0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [Finset.sum_range_succ,Polynomial.coeff_derivative,h4]
  ring

theorem two_root_derivative (P : Polynomial ℝ) (hP : P.natDegree≤3) (r s : ℝ)
    (hr : P.eval r=0) (hs : P.eval s=0) (hne : r≠s) :
    P.derivative.eval r=(r-s)*(P.coeff 2+P.coeff 3*(2*r+s)) := by
  have hf : (r-s)*(P.coeff 1+P.coeff 2*(r+s)+P.coeff 3*(r^2+r*s+s^2))=0 := by
    calc
      _ = P.eval r-P.eval s := by rw [eval_four P hP r,eval_four P hP s]; ring
      _ = 0 := by rw [hr,hs,sub_self]
  have hz := (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hne)
  rw [derivative_four P hP r]
  linear_combination hz

theorem derivative_distance (P : Polynomial ℝ) (hP : P.natDegree≤3) (r s U M : ℝ)
    (hr : P.eval r=0) (hs : P.eval s=0) (hne : r≠s)
    (hU : 0≤U) (_hM : 0≤M) (h2 : |P.coeff 2| ≤ U) (h3 : |P.coeff 3| ≤ U)
    (hrM : |r| ≤ M) (hsM : |s| ≤ M) :
    |P.derivative.eval r| ≤ |r-s| * (U*(1+3*M)) := by
  rw [two_root_derivative P hP r s hr hs hne,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hlin : |2*r+s| ≤ 3*M := by
    calc
      _ ≤ |2*r| + |s| := abs_add_le _ _
      _ = 2*|r| + |s| := by rw [abs_mul]; norm_num
      _ ≤ 3*M := by linarith
  calc
    _ ≤ |P.coeff 2| + |P.coeff 3| * |2*r+s| := by
      simpa only [abs_mul] using abs_add_le (P.coeff 2) (P.coeff 3*(2*r+s))
    _ ≤ U+U*(3*M) := add_le_add h2 (mul_le_mul h3 hlin (abs_nonneg _) hU)
    _ = U*(1+3*M) := by ring

end Blotto.PlayerSpecificEvaluationMagnitude
