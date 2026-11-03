import Blotto.PlayerSpecificRecognitionScanHandover

/-! Complete executing finite-bit parameter recognizer. Preparation and
scan are each executed once. On acceptance, the retained reduced scale is
computed once and the complete original input/output records are priced. -/
namespace Blotto.PlayerSpecificFiniteParameterExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificFiniteParameterReturn
set_option autoImplicit false
set_option maxHeartbeats 2000000

def copyResult (result : Option Result) : Trace :=
  match result with
  | none => [.control 0]
  | some r => PlayerSpecificCellTestConstruction.copyCell r.cell++
      PlayerSpecificCandidateSelection.copyCandidate r.root++copyRow r.scale++[.control 1]
def frame {N : ℕ} (i : RationalPlayerSpecificInput N) (result : Option Result) : Trace :=
  copyRow (PlayerSpecificRecognitionInputHeights.row i)++copyResult result++
    [.control N,.control (if result.isSome then 1 else 0)]
def run {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) : Option Result×ℕ :=
  let prepared:=PlayerSpecificRationalIntervalsExecution.run model i
  let selected:=PlayerSpecificRecognitionScanExecution.run model i.budget prepared.1
  match selected.1 with
  | none => (none,prepared.2+selected.2+price model (frame i none))
  | some chosen =>
    let scale:=PlayerSpecificFiniteScaleExecution.run model chosen.1 i.budget chosen.2.polynomial
    let result:Result:=⟨chosen.1,chosen.2,scale.1⟩
    (some result,prepared.2+selected.2+scale.2+price model (frame i (some result)))

theorem value {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).1=PlayerSpecificFiniteParameterReturn.run model i := by
  simp only [run,PlayerSpecificRationalIntervalsExecution.value,
    PlayerSpecificRecognitionScanExecution.value model i.budget i.budget_pos.ne',PlayerSpecificFiniteScaleExecution.value,
    PlayerSpecificFiniteParameterReturn.run,PlayerSpecificFiniteRecognition.run]
  cases PlayerSpecificFiniteRecognition.scan model i.budget (PlayerSpecificRationalIntervals.run i) with
  | none => rfl
  | some chosen => rfl

end Blotto.PlayerSpecificFiniteParameterExecution
