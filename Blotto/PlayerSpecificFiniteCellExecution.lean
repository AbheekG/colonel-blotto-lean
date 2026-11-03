import Blotto.PlayerSpecificBreakpointContract

/-! Complete priced finite-bit cell search. The cubic is constructed once,
its candidates are generated once, the interior scan is executed once, and
only its failure enters the separately priced rational breakpoint test. -/
namespace Blotto.PlayerSpecificFiniteCellExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def frame (c : Cell) (b : ℚ) (polynomial : Data) (rows : List Candidate) (result : Option Candidate) : Trace :=
  PlayerSpecificCellTestConstruction.copyCell c++copyRow [b]++copyRow polynomial++
    PlayerSpecificCandidateRows.copyRows rows++PlayerSpecificCandidateScanExecution.copyOption result++[.control rows.length]

def run (model : RationalCostModel) (c : Cell) (b : ℚ) : Option Candidate×ℕ :=
  let polynomial:=PlayerSpecificCubicConstruction.run c b
  let roots:=PlayerSpecificCandidateExecution.run model polynomial.1
  let interior:=PlayerSpecificCandidateScanExecution.run model c roots.1
  match interior.1 with
  | some r => (some r,price model polynomial.2+roots.2+interior.2+price model (frame c b polynomial.1 roots.1 (some r)))
  | none =>
    let boundary:=PlayerSpecificBreakpointExecution.run c b
    (boundary.1,price model polynomial.2+roots.2+interior.2+price model boundary.2+
      price model (frame c b polynomial.1 roots.1 boundary.1))

theorem value (model : RationalCostModel) (c : Cell) (b : ℚ) (hb : b≠0) :
    (run model c b).1=PlayerSpecificFiniteCellSearch.run model c b := by
  simp only [run,PlayerSpecificCubicConstruction.value,PlayerSpecificCandidateScanExecution.value,
    PlayerSpecificBreakpointExecution.value c b hb,PlayerSpecificFiniteCellSearch.run,
    PlayerSpecificFiniteCellSearch.interior,PlayerSpecificFiniteCellSearch.roots]
  cases (PlayerSpecificCandidateExecution.run model (cubic c.state.coefficients b)).1.find?
    (PlayerSpecificAlgebraicCandidateTest.run model c) <;> rfl

end Blotto.PlayerSpecificFiniteCellExecution
