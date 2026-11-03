import Blotto.PlayerSpecificSortTripleSourceCost
import Blotto.PlayerSpecificAlgebraicFourSpecDraw

/-! The unsorted four-variable input retains the measured three-length
sort, sorted six-field input, and exact permutation for restoration. -/
namespace Blotto.PlayerSpecificFourSpecInputExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourSpecInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (a : Input) : FixedArrayTable 6 Data :=
  FixedArrayTable.ofFn ![a.budget,a.lengths.read 0,a.lengths.read 1,a.lengths.read 2,
    a.mixtureLength,a.probability]

def selected (a : Input) (s : PlayerSpecificAlgebraicSortTriple.Prepared) : Prepared :=
  ⟨⟨a.budget,s.lengths.read 0,s.lengths.read 1,s.lengths.read 2,
      a.mixtureLength,a.probability⟩,s.permutation⟩

def frame (root : Candidate) (a : Input) (p : Prepared) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (environment a)
    (PlayerSpecificAlgebraicFourInput.environment p.input) ++
  List.ofFn (fun j : Fin 3 => Event.control (p.permutation j).val)

def run (root : Candidate) (a : Input) : Prepared × ℕ :=
  let model := RationalCostModel.schoolbook
  let sorted := PlayerSpecificSortTripleExecution.run root a.lengths
  let result := selected a sorted.1
  (result,sorted.2 + price model (frame root a result) + price model [.control 1])

theorem value (root : Candidate) (a : Input) :
    (run root a).1 = prepare RationalCostModel.schoolbook root a := by
  simp only [run, PlayerSpecificSortTripleExecution.value, selected, prepare]

end Blotto.PlayerSpecificFourSpecInputExecution
