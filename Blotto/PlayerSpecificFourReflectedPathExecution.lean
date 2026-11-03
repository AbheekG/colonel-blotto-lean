import Blotto.PlayerSpecificFourReflectedVisitedStates
import Blotto.PlayerSpecificFiniteResourceEntryExecution
import Blotto.PlayerSpecificAlgebraicFourReflectedPath

/-! The reflected branch prepares its three resources once and runs the
complete measured two-step finite resource engine once. -/
namespace Blotto.PlayerSpecificFourReflectedPathExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def runCached (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) :
    (PlayerSpecificAlgebraicFourReflectedInput.Prepared×(PlayerSpecificAlgebraicResourceState.State 3×ℕ))×ℕ :=
  let p:=PlayerSpecificFourReflectedInputExecution.run RationalCostModel.schoolbook r a
  let result:=PlayerSpecificFiniteResourceEntryExecution.draw p.1.resources true H bits
  ((p.1,result.1),p.2+result.2+price RationalCostModel.schoolbook [.control 1])

def run (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) : (PlayerSpecificAlgebraicResourceState.State 3×ℕ)×ℕ :=
  let result:=runCached r a H bits
  (result.1.2,result.2)

theorem cached_input_value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) :
    (runCached r a H bits).1.1=PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a := by
  simp only [runCached,PlayerSpecificFourReflectedInputExecution.value]

theorem cached_state_value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) :
    (runCached r a H bits).1.2=PlayerSpecificAlgebraicFourReflectedPath.draw r a H bits := by
  simp only [runCached,PlayerSpecificFourReflectedInputExecution.value,
    PlayerSpecificFiniteResourceEntryExecution.value,PlayerSpecificAlgebraicFourReflectedPath.draw]

theorem cached_cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) : (runCached r a H bits).2=(run r a H bits).2 := rfl

theorem value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) :
    (run r a H bits).1=PlayerSpecificAlgebraicFourReflectedPath.draw r a H bits := by
  exact cached_state_value r a H bits

theorem price_equation (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H : ℕ)
    (bits : Fin (2*H) → Bool) :
    (run r a H bits).2=(PlayerSpecificFourReflectedInputExecution.run RationalCostModel.schoolbook r a).2+
      (PlayerSpecificFiniteResourceEntryExecution.draw
        (PlayerSpecificAlgebraicFourReflectedInput.prepare RationalCostModel.schoolbook r a).resources
        true H bits).2+2 := by
  simp only [run,runCached,PlayerSpecificFourReflectedInputExecution.value]
  rfl

end Blotto.PlayerSpecificFourReflectedPathExecution
