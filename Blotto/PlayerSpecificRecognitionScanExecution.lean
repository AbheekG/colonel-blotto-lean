import Blotto.PlayerSpecificFiniteCellHandover

/-! Actual priced first-passing rational-cell scan. Full input-cell lists,
selected cell/root records and the budget/control words are accounted for
at every caller frame, including complete rejection. -/
namespace Blotto.PlayerSpecificRecognitionScanExecution
open PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def copyCells (cells : List Cell) : Trace :=
  [.control cells.length]++cells.flatMap PlayerSpecificCellTestConstruction.copyCell
def copyResult (result : Option (Cell×Candidate)) : Trace :=
  match result with
  | none => [.control 0]
  | some (c,r) => PlayerSpecificCellTestConstruction.copyCell c++
      PlayerSpecificCandidateSelection.copyCandidate r++[.control 1]
def frame (b : ℚ) (cells : List Cell) (result : Option (Cell×Candidate)) : Trace :=
  copyCells cells++copyResult result++copyRow [b]++[.control cells.length,.control (if result.isSome then 1 else 0)]
def run (model : RationalCostModel) (b : ℚ) : List Cell → Option (Cell×Candidate)×ℕ
  | [] => (none,price model (frame b [] none))
  | c::cs =>
    let tested:=PlayerSpecificFiniteCellExecution.run model c b
    match tested.1 with
    | some r => (some (c,r),tested.2+price model (frame b (c::cs) (some (c,r))))
    | none =>
      let rest:=run model b cs
      (rest.1,tested.2+rest.2+price model (frame b (c::cs) rest.1))

theorem value (model : RationalCostModel) (b : ℚ) (hb : b≠0) (cells : List Cell) :
    (run model b cells).1=PlayerSpecificFiniteRecognition.scan model b cells := by
  induction cells with
  | nil => rfl
  | cons c cs ih =>
    simp only [run,PlayerSpecificFiniteCellExecution.value model c b hb,PlayerSpecificFiniteRecognition.scan,ih]
    cases PlayerSpecificFiniteCellSearch.run model c b <;> rfl

theorem returned (model : RationalCostModel) (b : ℚ) (cells : List Cell) (c : Cell) (r : Candidate)
    (hr : (run model b cells).1=some (c,r)) :
    c∈cells ∧ (PlayerSpecificFiniteCellExecution.run model c b).1=some r := by
  induction cells with
  | nil => cases hr
  | cons d ds ih =>
    simp only [run] at hr
    split at hr
    · rename_i root hroot
      have he:=Option.some.inj hr
      have hc : d=c := congrArg Prod.fst he
      have hrepr : root=r := congrArg Prod.snd he
      subst d
      subst root
      exact ⟨List.mem_cons_self,hroot⟩
    · have ht:=ih hr
      exact ⟨List.mem_cons_of_mem d ht.1,ht.2⟩

end Blotto.PlayerSpecificRecognitionScanExecution
