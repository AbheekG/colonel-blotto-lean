import Blotto.PlayerSpecificCandidateRows

/-! Complete executing irreducible-candidate preparation. Rational factors
and the original isolating intervals are computed once each; the retained
lists feed the priced candidate continuation directly. -/
namespace Blotto.PlayerSpecificCandidateExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (model : RationalCostModel) (p : Data) : List Candidate×ℕ :=
  let factors:=PlayerSpecificFactorContract.run model p
  let intervals:=PlayerSpecificRootExecution.run model p
  let candidates:=PlayerSpecificCandidateRows.run model factors.1.1 factors.1.2 intervals.1
  (candidates.1,factors.2+intervals.2+candidates.2+price model (copyRow p)+
    price model (copyRow factors.1.1)+price model (copyRow factors.1.2)+
    price model (PlayerSpecificForestExecution.copyForest intervals.1)+
    price model (PlayerSpecificCandidateRows.copyRows candidates.1)+price model [.control 4])

theorem value (model : RationalCostModel) (p : Data) : (run model p).1=PlayerSpecificAlgebraicCandidates.run p := by
  simp only [run,PlayerSpecificCandidateRows.value,PlayerSpecificFactorContract.value,
    PlayerSpecificRootExecution.value,PlayerSpecificAlgebraicCandidates.run]

end Blotto.PlayerSpecificCandidateExecution
