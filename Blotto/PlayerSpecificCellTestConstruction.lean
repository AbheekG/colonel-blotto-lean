import Blotto.PlayerSpecificPolynomialSignContract

/-! Actual traced construction of every candidate-test polynomial. All
negations, multiplications, subtraction, cell reads and returned rows are
included, including the optional rational upper boundary. -/
namespace Blotto.PlayerSpecificCellTestConstruction
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Result where
  positive : Data
  lower : Data
  upper : Option Data
  first : Data
  second : Data

def copyCell (c : Cell) : Trace :=
  copyRow [c.state.coefficients.A1,c.state.coefficients.A2,c.state.coefficients.B1,c.state.coefficients.B2,
    c.state.prefixMax,c.lower,c.suffixMax]++copyRow c.upper.toList++[.control 1]
def copyResult (r : Result) : Trace :=
  copyRow r.positive++copyRow r.lower++copyRow r.first++copyRow r.second++
    (match r.upper with | none => [.control 0] | some row => copyRow row++[.control 1])
def run (c : Cell) : Result×Trace :=
  let low:=scalar .multiply (-1) c.lower
  let prefixValue:=scalar .multiply 2 c.state.prefixMax
  let firstValue:=scalar .subtract c.state.coefficients.B2 prefixValue.1
  let suffixValue:=scalar .multiply (-2) c.suffixMax
  let result:Result:=⟨[0,1],[low.1,1],c.upper.map (fun q => [q,-1]),
    [firstValue.1,0,c.state.coefficients.B1],[c.state.coefficients.B2,suffixValue.1,c.state.coefficients.B1]⟩
  (result,copyCell c++low.2++prefixValue.2++firstValue.2++suffixValue.2++copyResult result++[.control 5])

theorem values (c : Cell) :
    (run c).1.positive=PlayerSpecificAlgebraicCellTests.positive ∧
      (run c).1.lower=PlayerSpecificAlgebraicCellTests.lower c ∧
      (run c).1.upper=c.upper.map PlayerSpecificAlgebraicCellTests.upper ∧
      (run c).1.first=PlayerSpecificAlgebraicCellTests.firstGate c ∧
      (run c).1.second=PlayerSpecificAlgebraicCellTests.secondGate c := by
  simp only [run,scalar,Arithmetic.apply,neg_one_mul,PlayerSpecificAlgebraicCellTests.positive,
    PlayerSpecificAlgebraicCellTests.lower,
    PlayerSpecificAlgebraicCellTests.firstGate,PlayerSpecificAlgebraicCellTests.secondGate,and_self]
  exact ⟨trivial,trivial,rfl,trivial⟩

end Blotto.PlayerSpecificCellTestConstruction
