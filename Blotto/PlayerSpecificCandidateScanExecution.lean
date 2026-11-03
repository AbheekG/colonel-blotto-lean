import Blotto.PlayerSpecificCandidateRecordCost

/-! The exact first-passing scan executes the priced candidate test and
copies all input, optional result and enclosing rational-cell records. -/
namespace Blotto.PlayerSpecificCandidateScanExecution
open PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def copyOption (candidate : Option Candidate) : Trace :=
  match candidate with
  | none => [.control 0]
  | some r => PlayerSpecificCandidateSelection.copyCandidate r++[.control 1]
def frame (c : Cell) (rows : List Candidate) (result : Option Candidate) : Trace :=
  PlayerSpecificCellTestConstruction.copyCell c++PlayerSpecificCandidateRows.copyRows rows++copyOption result++
    [.control rows.length,.control (if result.isSome then 1 else 0)]
def run (model : RationalCostModel) (c : Cell) : List Candidate → Option Candidate×ℕ
  | [] => (none,price model (frame c [] none))
  | r::rs =>
    let tested:=PlayerSpecificCandidateTestExecution.run model c r
    if tested.1 then
      (some r,tested.2+price model (frame c (r::rs) (some r)))
    else
      let rest:=run model c rs
      (rest.1,tested.2+rest.2+price model (frame c (r::rs) rest.1))

theorem value (model : RationalCostModel) (c : Cell) (rows : List Candidate) :
    (run model c rows).1=rows.find? (PlayerSpecificAlgebraicCandidateTest.run model c) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    cases ht : PlayerSpecificAlgebraicCandidateTest.run model c r <;>
      simp only [run,PlayerSpecificCandidateTestExecution.value,ht,Bool.false_eq_true,ite_false,ite_true,List.find?_cons,ih]

theorem returned_mem (model : RationalCostModel) (c : Cell) (rows : List Candidate)
    (r : Candidate) (hr : r∈(run model c rows).1) : r∈rows := by
  rw [value] at hr
  exact List.mem_of_find?_eq_some hr

end Blotto.PlayerSpecificCandidateScanExecution
