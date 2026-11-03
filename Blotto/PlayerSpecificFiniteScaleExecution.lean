import Blotto.PlayerSpecificFiniteCellContract

/-! The retained algebraic scale is actually computed from two rational
budget operations and a three-position modular Horner loop. All enclosing
cell, field-polynomial, seed, numerator and return copies are included. -/
namespace Blotto.PlayerSpecificFiniteScaleExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1500000

def frame (c : Cell) (b : ℚ) (m seed numerator result : Data) : Trace :=
  PlayerSpecificCellTestConstruction.copyCell c++copyRow [b]++copyRow m++copyRow seed++copyRow numerator++copyRow result++[.control 3]
def run (model : RationalCostModel) (c : Cell) (b : ℚ) (m : Data) : Data×ℕ :=
  let denominator:=scalar .multiply 2 b
  let reciprocal:=scalar .divide 1 denominator.1
  let seed:=[reciprocal.1]
  let numerator:=[c.state.coefficients.B2,0,c.state.coefficients.B1]
  let result:=PlayerSpecificModularExecution.run model m seed numerator
  (result.1,price model denominator.2+price model reciprocal.2+result.2+
    price model (frame c b m seed numerator result.1))

theorem value (model : RationalCostModel) (c : Cell) (b : ℚ) (m : Data) :
    (run model c b m).1=PlayerSpecificFiniteParameterReturn.scale c b m := by
  simp only [run,PlayerSpecificModularExecution.value,scalar,Arithmetic.apply,PlayerSpecificFiniteParameterReturn.scale]

end Blotto.PlayerSpecificFiniteScaleExecution
