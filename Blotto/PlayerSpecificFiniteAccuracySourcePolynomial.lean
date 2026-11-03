import Blotto.PlayerSpecificFiniteAccuracySourceCost

/-! A polynomial in dimension, supplied minimum exponent and rational
epsilon word length bounds the actual three-precision source program. -/
namespace Blotto.PlayerSpecificFiniteAccuracySourcePolynomial
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputSize (N s : ℕ) (epsilon : ℚ) : ℕ :=
  N+s+rationalWordWidth epsilon+1000

def sizeBound (N s : ℕ) (epsilon : ℚ) : ℕ :=
  100*inputSize N s epsilon

def polynomial (N s : ℕ) (epsilon : ℚ) : ℕ :=
  let S:=sizeBound N s epsilon
  let W:=4*S+40
  4000*(S+1)*(W*W+W)

theorem size_le (N s : ℕ) (epsilon : ℚ) :
    PlayerSpecificFiniteAccuracySourceCost.size N s epsilon≤
      sizeBound N s epsilon := by
  let X:=inputSize N s epsilon
  have hscale : PlayerSpecificFiniteAccuracySourceCost.scale N≤32*X := by
    dsimp only [PlayerSpecificFiniteAccuracySourceCost.scale,X,inputSize]
    omega
  have hw:=control_width (PlayerSpecificFiniteAccuracySourceCost.scale N)
  have hwidth : binaryWordWidth (PlayerSpecificFiniteAccuracySourceCost.scale N)≤32*X+1 := by
    omega
  have hX : 1000≤X := by dsimp only [X,inputSize]; omega
  dsimp only [PlayerSpecificFiniteAccuracySourceCost.size,
    PlayerSpecificRationalPrecisionSourceSizes.inputWidth,sizeBound]
  dsimp only [X,inputSize] at hscale hwidth hX ⊢
  omega

theorem work_bound (N s : ℕ) (epsilon : ℚ) :
    PlayerSpecificFiniteAccuracySourceCost.work N s epsilon≤
      polynomial N s epsilon := by
  let S:=PlayerSpecificFiniteAccuracySourceCost.size N s epsilon
  let V:=sizeBound N s epsilon
  let W:=PlayerSpecificFiniteAccuracySourceCost.width N s epsilon
  let Z:=4*V+40
  have hS : S≤V := size_le N s epsilon
  have hW : W≤Z := by dsimp only [W,Z,PlayerSpecificFiniteAccuracySourceCost.width]; omega
  have hrate:=RationalCostModel.schoolbook.monotone hW
  have hproduct:=Nat.mul_le_mul
    (Nat.add_le_add_right hS 1) hrate
  have hscaled:=Nat.mul_le_mul_left 4000 hproduct
  simpa only [PlayerSpecificFiniteAccuracySourceCost.work,polynomial,
    RationalCostModel.schoolbook,S,V,W,Z,mul_assoc] using hscaled

theorem polynomial_mono_exponent (N : ℕ) (epsilon : ℚ) {s t : ℕ}
    (h : s≤t) : polynomial N s epsilon≤polynomial N t epsilon := by
  have hX : inputSize N s epsilon ≤ inputSize N t epsilon := by
    dsimp only [inputSize]
    omega
  have hS : sizeBound N s epsilon≤sizeBound N t epsilon :=
    Nat.mul_le_mul_left 100 hX
  simp only [polynomial]
  gcongr

theorem source_cost (N s : ℕ) (epsilon : ℚ) (he : 0<epsilon) :
    (PlayerSpecificFiniteAccuracyExecution.run N s epsilon).2≤
      polynomial N s epsilon :=
  (PlayerSpecificFiniteAccuracySourceCost.cost N s epsilon he).trans
    (work_bound N s epsilon)

end Blotto.PlayerSpecificFiniteAccuracySourcePolynomial
