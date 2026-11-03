import Blotto.PlayerSpecificReflectAppendSourceCost
import Blotto.PlayerSpecificBitSlicePolynomial
import Blotto.PlayerSpecificNestedTerminalDrawSourceCost

/-! The full reflected component retains both addressed bit blocks, one
resource preparation/path, one terminal record, one nested draw and one
coordinate reflection. -/
namespace Blotto.PlayerSpecificFourReflectedDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((2*H)+((17*H+K)+K)) → Bool) : FixedArrayTable 4 Data×ℕ :=
  let model:=RationalCostModel.schoolbook
  let M:=(2*H)+((17*H+K)+K)
  let head:=PlayerSpecificBitSliceExecution.run model M 0 (2*H) (by omega) bits
  let inner:=PlayerSpecificBitSliceExecution.run model M (2*H) ((17*H+K)+K) (by omega) bits
  let path:=PlayerSpecificFourReflectedPathExecution.runCached r a H head.1
  let terminal:=PlayerSpecificFourReflectedTerminalExecution.run model r.root path.1.1 path.1.2.1
  let sampled:=PlayerSpecificNestedTerminalDrawExecution.run model r.root terminal.1 H K inner.1
  let reflected:=PlayerSpecificReflectAppendExecution.run model r.root path.1.1.long sampled.1
  (reflected.1,head.2+inner.2+path.2+terminal.2+sampled.2+reflected.2+price model [.control 1])

theorem value (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (H K : ℕ)
    (bits : Fin ((2*H)+((17*H+K)+K)) → Bool) :
    (run r a H K bits).1=PlayerSpecificAlgebraicFourReflectedDraw.draw r a H K bits := by
  simp only [run,PlayerSpecificBitSliceExecution.first_value,
    PlayerSpecificBitSliceExecution.second_value,
    PlayerSpecificFourReflectedPathExecution.cached_input_value,
    PlayerSpecificFourReflectedPathExecution.cached_state_value,
    PlayerSpecificFourReflectedTerminalExecution.value,
    PlayerSpecificNestedTerminalDrawExecution.value,
    PlayerSpecificReflectAppendExecution.value,
    PlayerSpecificAlgebraicFourReflectedDraw.draw,
    PlayerSpecificAlgebraicFourReflectedPath.draw,
    PlayerSpecificAlgebraicFourReflectedTerminal.input]

end Blotto.PlayerSpecificFourReflectedDrawExecution
