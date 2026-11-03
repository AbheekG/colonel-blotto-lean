import Blotto.PlayerSpecificPolynomialSignExecution

/-! Literal rational polynomials for all candidate interval/endpoint tests.
The endpoint gate is two quadratic nonnegativity tests, avoiding division
or maxima in the actual algebraic acceptance computation. -/
namespace Blotto.PlayerSpecificAlgebraicCellTests
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

def positive : Data := [0,1]
def lower (c : Cell) : Data := [-c.lower,1]
def upper (q : ℚ) : Data := [q,-1]
def firstGate (c : Cell) : Data := [c.state.coefficients.B2-2*c.state.prefixMax,0,c.state.coefficients.B1]
def secondGate (c : Cell) : Data := [c.state.coefficients.B2,-2*c.suffixMax,c.state.coefficients.B1]

theorem positive_value (x : ℝ) : realEvaluate positive x=x := by
  simp only [positive,realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_zero,Rat.cast_one,mul_zero,mul_one,add_zero,zero_add]
theorem lower_value (c : Cell) (x : ℝ) : realEvaluate (lower c) x=x-(c.lower:ℝ) := by
  simp only [lower,realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_neg,Rat.cast_one,mul_zero,mul_one,add_zero]
  ring
theorem upper_value (q : ℚ) (x : ℝ) : realEvaluate (upper q) x=(q:ℝ)-x := by
  simp only [upper,realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_neg,Rat.cast_one,mul_zero,mul_neg_one,add_zero]
  ring
theorem first_value (c : Cell) (x : ℝ) : realEvaluate (firstGate c) x=
    (c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ)-2*(c.state.prefixMax:ℝ) := by
  simp only [firstGate,realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_zero,mul_zero,add_zero,zero_add]
  ring
theorem second_value (c : Cell) (x : ℝ) : realEvaluate (secondGate c) x=
    (c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ)-2*(c.suffixMax:ℝ)*x := by
  simp only [secondGate,realEvaluate,List.foldr_cons,List.foldr_nil,Rat.cast_mul,Rat.cast_neg,Rat.cast_ofNat,mul_zero,add_zero]
  ring

theorem gates_iff (c : Cell) (b : ℚ) (hb : b≠0) (x : ℝ) :
    (0≤realEvaluate (firstGate c) x ∧ 0≤realEvaluate (secondGate c) x) ↔
      PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x := by
  have hbR : (b:ℝ)≠0 := by exact_mod_cast hb
  rw [first_value,second_value,PlayerSpecificCellCandidates.Passes,max_le_iff]
  have hs : (b:ℝ)*PlayerSpecificCubic.candidateScale (castCell c).state.coefficients (b:ℝ) x=
      ((c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ))/2 := by
    unfold PlayerSpecificCubic.candidateScale castCell castState castCoefficients
    field_simp
  rw [hs]
  change (0≤(c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ)-2*(c.state.prefixMax:ℝ) ∧
      0≤(c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ)-2*(c.suffixMax:ℝ)*x) ↔
    (c.state.prefixMax:ℝ)≤((c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ))/2 ∧
      x*(c.suffixMax:ℝ)≤((c.state.coefficients.B1:ℝ)*x^2+(c.state.coefficients.B2:ℝ))/2
  constructor <;> intro h <;> constructor <;> nlinarith only [h.1,h.2]

end Blotto.PlayerSpecificAlgebraicCellTests
