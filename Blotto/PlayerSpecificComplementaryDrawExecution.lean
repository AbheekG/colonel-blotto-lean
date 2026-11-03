import Blotto.PlayerSpecificFourSpecDrawSourceCost
import Blotto.PlayerSpecificMidpointCost
import Blotto.PlayerSpecificAlgebraicComplementaryDraw

/-! Two-uniform-group terminal sampling computes the finite midpoint,
constant field row, product and budget complement once each. -/
namespace Blotto.PlayerSpecificComplementaryDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (budget : Data) : FixedArrayTable 1 Data :=
  FixedArrayTable.ofFn (fun _ => budget)

def run (root : Candidate) (budget : Data) (K : ℕ) (bits : Fin K → Bool) :
    FixedArrayTable 4 Data × ℕ :=
  let model := RationalCostModel.schoolbook
  let midpoint := PlayerSpecificMidpointExecution.run model K bits
  let q := PlayerSpecificFieldCombinationContract.constant root.polynomial midpoint.1
  let first := PlayerSpecificAlgebraicExpressionExecution.binary model root .multiply budget q.1
  let second := PlayerSpecificAlgebraicExpressionExecution.binary model root .subtract budget first.1
  let result := FixedArrayTable.ofFn ![first.1,second.1,[],[]]
  (result, midpoint.2 + price model q.2 + first.2 + second.2 +
    price model (PlayerSpecificExpressionVectorExecution.frame root (environment budget) result) +
    price model [.control 1])

theorem value (root : Candidate) (budget : Data) (K : ℕ) (bits : Fin K → Bool) :
    (run root budget K bits).1 = PlayerSpecificAlgebraicComplementaryDraw.draw root budget K bits := by
  simp only [run, PlayerSpecificMidpointExecution.value,
    PlayerSpecificFieldCombinationContract.constant_value,
    PlayerSpecificAlgebraicExpressionExecution.binary_value,
    PlayerSpecificAlgebraicComplementaryDraw.draw]

end Blotto.PlayerSpecificComplementaryDrawExecution
