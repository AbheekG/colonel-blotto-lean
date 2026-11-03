import Blotto.PlayerSpecificCellTestConstructionCost

/-! Priced exact interior acceptance. The five comparison polynomials are
constructed once, and each actual algebraic sign, returned tag and caller
copy is included. Optional upper endpoints retain their separate branch. -/
namespace Blotto.PlayerSpecificCandidateTestExecution
open SignType PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def signWord : SignType → ℕ | .neg => 0 | .zero => 1 | .pos => 2
def upperRun (model : RationalCostModel) (candidate : Candidate) (row : Option Data) : Bool×ℕ :=
  match row with
  | none => (true,price model [.control 0])
  | some p =>
    let result:=PlayerSpecificPolynomialSignExecution.run model candidate.polynomial p candidate.interval
    (decide (result.1=.pos),result.2+price model [.control (signWord result.1),.control 1])

def frame (candidate : Candidate) (a b d e : SignType) (upper accepted : Bool) : Trace :=
  copyRow candidate.polynomial++copyRow [candidate.interval.lo,candidate.interval.hi]++
    [.control (signWord a),.control (signWord b),.control (signWord d),.control (signWord e),
      .control (if upper then 1 else 0),.control (if accepted then 1 else 0),.control 5]

def run (model : RationalCostModel) (c : Cell) (candidate : Candidate) : Bool×ℕ :=
  let tests:=PlayerSpecificCellTestConstruction.run c
  let a:=PlayerSpecificPolynomialSignExecution.run model candidate.polynomial tests.1.positive candidate.interval
  let b:=PlayerSpecificPolynomialSignExecution.run model candidate.polynomial tests.1.lower candidate.interval
  let u:=upperRun model candidate tests.1.upper
  let d:=PlayerSpecificPolynomialSignExecution.run model candidate.polynomial tests.1.first candidate.interval
  let e:=PlayerSpecificPolynomialSignExecution.run model candidate.polynomial tests.1.second candidate.interval
  let accepted:=decide (a.1=.pos) && decide (b.1=.pos) && u.1 &&
    PlayerSpecificAlgebraicCandidateTest.nonnegative d.1 && PlayerSpecificAlgebraicCandidateTest.nonnegative e.1
  (accepted,price model tests.2+a.2+b.2+u.2+d.2+e.2+
    price model (frame candidate a.1 b.1 d.1 e.1 u.1 accepted))

theorem upper_value (model : RationalCostModel) (c : Cell) (candidate : Candidate) :
    (upperRun model candidate (PlayerSpecificCellTestConstruction.run c).1.upper).1=
      PlayerSpecificAlgebraicCandidateTest.upperTest model candidate c.upper := by
  rw [(PlayerSpecificCellTestConstruction.values c).2.2.1]
  cases c.upper <;> rfl

theorem value (model : RationalCostModel) (c : Cell) (candidate : Candidate) :
    (run model c candidate).1=PlayerSpecificAlgebraicCandidateTest.run model c candidate := by
  have hv:=PlayerSpecificCellTestConstruction.values c
  simp only [run,upper_value,hv.1,hv.2.1,hv.2.2.2.1,hv.2.2.2.2]
  rfl

end Blotto.PlayerSpecificCandidateTestExecution
