import Blotto.PlayerSpecificDepthExecution

/-! Actual integer root preparation from original rational coefficients.
Polynomial data and all three encoded heights are computed and cached; no
enclosure, separation, precision, width or source-price oracle is supplied. -/
namespace Blotto.PlayerSpecificIntegerPreparation
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

structure Result where
  polynomials : PlayerSpecificPolynomialPreparation.Result
  magnitude : ℕ
  separation : ℕ
  depth : ℕ

def run (model : RationalCostModel) (p : Data) : Result×ℕ :=
  let prepared := PlayerSpecificPolynomialPreparation.run p
  let originalWidth := PlayerSpecificInputWidthExecution.run model p
  let squarefreeWidth := PlayerSpecificInputWidthExecution.run model prepared.1.polynomial
  let certificateWidth := PlayerSpecificInputWidthExecution.run model prepared.1.unitRight
  let magnitude := PlayerSpecificEnclosureExecution.run model originalWidth.1
  let precision := PlayerSpecificDepthExecution.run model magnitude.1 squarefreeWidth.1 certificateWidth.1 prepared.1.unitRight.length
  let result : Result := ⟨prepared.1,magnitude.1,precision.1.1,precision.1.2⟩
  (result,price model prepared.2+originalWidth.2+squarefreeWidth.2+certificateWidth.2+magnitude.2+precision.2+
    price model (copyRow result.polynomials.polynomial++copyRow result.polynomials.unitRight++
      PlayerSpecificSturmExecution.copyRows result.polynomials.rows)+
    32*(4+binaryWordWidth p.length+binaryWordWidth result.magnitude+binaryWordWidth result.separation+binaryWordWidth result.depth))

theorem polynomial_values (model : RationalCostModel) (p : Data) :
    (run model p).1.polynomials.polynomial=PlayerSpecificSquarefreeAlgorithm.run p ∧
      (run model p).1.polynomials.unitRight=PlayerSpecificSquarefreeCoprime.unitRight p ∧
      (run model p).1.polynomials.rows=PlayerSpecificSturmRootCount.rows p := PlayerSpecificPolynomialPreparation.values p

theorem magnitude_value (model : RationalCostModel) (p : Data) :
    (run model p).1.magnitude=PlayerSpecificRootMagnitude.rootBound p := by
  simp only [run,PlayerSpecificEnclosureExecution.value,PlayerSpecificInputWidthExecution.value,PlayerSpecificRootMagnitude.rootBound]

theorem separation_value (model : RationalCostModel) (p : Data) :
    (run model p).1.separation=PlayerSpecificRootSeparation.separationDenominator p := by
  simp only [run,(PlayerSpecificDepthExecution.values model _ _ _ _).1,PlayerSpecificEnclosureExecution.value,
    PlayerSpecificInputWidthExecution.value,(PlayerSpecificPolynomialPreparation.values p).1,
    (PlayerSpecificPolynomialPreparation.values p).2.1,PlayerSpecificRootSeparation.separationDenominator,
    PlayerSpecificRootSeparation.derivativeBound,PlayerSpecificRootSeparation.bezoutBound,PlayerSpecificRootMagnitude.rootBound]

theorem depth_value (model : RationalCostModel) (p : Data) :
    (run model p).1.depth=PlayerSpecificRootIsolation.depth p := by
  simp only [run,(PlayerSpecificDepthExecution.values model _ _ _ _).2,PlayerSpecificEnclosureExecution.value,
    PlayerSpecificInputWidthExecution.value,(PlayerSpecificPolynomialPreparation.values p).1,
    (PlayerSpecificPolynomialPreparation.values p).2.1,PlayerSpecificRootIsolation.depth,
    PlayerSpecificRootSeparation.separationDenominator,PlayerSpecificRootSeparation.derivativeBound,
    PlayerSpecificRootSeparation.bezoutBound,PlayerSpecificRootMagnitude.rootBound]

end Blotto.PlayerSpecificIntegerPreparation
