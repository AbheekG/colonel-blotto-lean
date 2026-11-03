import Blotto.PlayerSpecificFourSpecInputSourceCost

/-! The measured unsorted four-variable draw keeps the sort result,
executes the ordered sampler once and restores all four coordinates. -/
namespace Blotto.PlayerSpecificFourSpecDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicFourSpecInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def restored (p : Prepared) (y : FixedArrayTable 4 Data) : FixedArrayTable 4 Data :=
  PlayerSpecificAlgebraicPermutation.permute
    (rationalPermutationWithLast p.permutation).symm y

def frame (root : PlayerSpecificAlgebraicCandidates.Candidate) (p : Prepared)
    (y z : FixedArrayTable 4 Data) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root y z ++
    List.ofFn (fun j : Fin 4 =>
      Event.control ((rationalPermutationWithLast p.permutation).symm j).val)

def run (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) : FixedArrayTable 4 Data × ℕ :=
  let model := RationalCostModel.schoolbook
  let prepared := PlayerSpecificFourSpecInputExecution.run r.root a
  let ordered := PlayerSpecificOrderedFourDrawExecution.run r prepared.1.input H K bits
  let result := restored prepared.1 ordered.1
  (result, prepared.2 + ordered.2 + price model (frame r.root prepared.1 ordered.1 result) +
    price model [.control 1])

theorem value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((80*H+K)+K) → Bool) :
    (run r a H K bits).1 = PlayerSpecificAlgebraicFourSpecDraw.draw r a H K bits := by
  simp only [run, restored, PlayerSpecificFourSpecInputExecution.value,
    PlayerSpecificOrderedFourDrawExecution.value, PlayerSpecificAlgebraicFourSpecDraw.draw]

end Blotto.PlayerSpecificFourSpecDrawExecution
