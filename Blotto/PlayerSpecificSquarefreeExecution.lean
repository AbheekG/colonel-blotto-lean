import Blotto.PlayerSpecificEuclideanContract

/-! Executed squarefree preprocessing: derivative, Euclidean GCD and
quotient, with all returned coefficient copies and control fields. -/
namespace Blotto.PlayerSpecificSquarefreeExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (p : Data) : Data×Trace :=
  let differentiated := PlayerSpecificDenseExecution.derivative p
  let common := PlayerSpecificGCDExecution.run p differentiated.1
  let divided := PlayerSpecificDivisionExecution.run p common.1
  (divided.1.1,copyRow p++differentiated.2++common.2++divided.2++copyRow divided.1.1++[.control p.length])

theorem value (p : Data) : (run p).1=PlayerSpecificSquarefreeAlgorithm.run p := by
  simp only [run,PlayerSpecificDenseExecution.derivative_value,PlayerSpecificGCDExecution.value,
    PlayerSpecificDivisionExecution.value,PlayerSpecificSquarefreeAlgorithm.run,PlayerSpecificSquarefreeAlgorithm.gcdDerivative]

theorem bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    HasHeight (run p).1 (PlayerSpecificSquarefreeHeights.quotientHeight H) ∧ (run p).1.length≤4 := by
  rw [value]
  exact PlayerSpecificSquarefreeHeights.quotient_bounds p H hp hH hlen

theorem roots (p : Data) (hp : semantics p≠0) (x : ℝ) :
    PlayerSpecificSturmVariations.realEvaluate (run p).1 x=0 ↔ PlayerSpecificSturmVariations.realEvaluate p x=0 := by
  rw [value]
  exact PlayerSpecificSquarefreeAlgorithm.evaluated_roots_preserved p hp x

end Blotto.PlayerSpecificSquarefreeExecution
