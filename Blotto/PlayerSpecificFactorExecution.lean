import Blotto.PlayerSpecificLinearFactorExecution

/-! The actual factor-removal entry runs the priced cached rational-root
enumerator and priced dense division at every step. It copies every retained
input, candidate list, returned factor list and residual, including controls. -/
namespace Blotto.PlayerSpecificFactorExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 3000000

def frame (fuel : ℕ) (p roots : Data) (result : Data×Data) : Trace :=
  copyRow p++copyRow roots++copyRow result.1++copyRow result.2++
    [.control fuel,.control roots.length,.control result.1.length]

def run (model : RationalCostModel) : ℕ → Data → (Data×Data)×ℕ
  | 0,p =>
    let residual:=PlayerSpecificDenseExecution.trim p
    let result:=([],residual.1)
    (result,price model residual.2+price model (frame 0 p [] result))
  | fuel+1,p =>
    let roots:=PlayerSpecificRationalRootExecution.run model p
    match roots.1 with
    | [] =>
      let residual:=PlayerSpecificDenseExecution.trim p
      let result:=([],residual.1)
      (result,roots.2+price model residual.2+price model (frame (fuel+1) p roots.1 result))
    | q::_ =>
      let linear:=PlayerSpecificLinearFactorExecution.run q
      let divided:=PlayerSpecificDivisionExecution.run p linear.1
      let rest:=run model fuel divided.1.1
      let result:=(q::rest.1.1,rest.1.2)
      (result,roots.2+price model linear.2+price model divided.2+rest.2+
        price model (frame (fuel+1) p roots.1 result))

theorem value (model : RationalCostModel) (fuel : ℕ) (p : Data) :
    (run model fuel p).1=PlayerSpecificRationalFactors.run fuel p := by
  induction fuel generalizing p with
  | zero => exact congrArg (fun q : Data => ([],q)) (PlayerSpecificDenseExecution.trim_value p)
  | succ fuel ih =>
    cases hr : PlayerSpecificRationalRoots.run p <;>
      simp only [run,PlayerSpecificRationalFactors.run,PlayerSpecificRationalRootExecution.value,hr,
        PlayerSpecificDenseExecution.trim_value,ih,PlayerSpecificDivisionExecution.value,
        PlayerSpecificLinearFactorExecution.value,PlayerSpecificLinearFactor.quotient]

end Blotto.PlayerSpecificFactorExecution
