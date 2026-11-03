import Blotto.PlayerSpecificAlgebraicRequestCost
import Blotto.PlayerSpecificNaturalExecution

/-! The native midpoint's balanced array decoder with actual natural
arithmetic, saved indices/results and conservative Boolean-buffer copies.
Each low/high block is decoded once; no exponential bit enumeration occurs. -/
namespace Blotto.PlayerSpecificBalancedPayloadExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (model : RationalCostModel) (buffer : Array Bool) (pos length result : ℕ) : ℕ :=
  price model (PlayerSpecificAlgebraicCallerFrame.run [] [buffer.size,pos,length,result])+buffer.size+1

def run (model : RationalCostModel) (buffer : Array Bool) (pos length : ℕ) : ℕ×ℕ :=
  if length=0 then (0,frame model buffer pos length 0) else
  if length=1 then
    let result:=if buffer.getD pos false then 1 else 0
    (result,frame model buffer pos length result) else
    let low:=PlayerSpecificNaturalExecution.binary model (fun a b => a/b) length 2
    let highLength:=PlayerSpecificNaturalExecution.binary model (fun a b => a-b) length low.1
    let highPos:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) pos low.1
    let lower:=run model buffer pos low.1
    let upper:=run model buffer highPos.1 highLength.1
    let shifted:=PlayerSpecificNaturalExecution.binary model Nat.shiftLeft upper.1 low.1
    let added:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) lower.1 shifted.1
    (added.1,low.2+highLength.2+highPos.2+lower.2+upper.2+shifted.2+added.2+
      frame model buffer pos length added.1)
termination_by length
decreasing_by all_goals simp only [PlayerSpecificNaturalExecution.binary_value]; omega

theorem value (model : RationalCostModel) (buffer : Array Bool) (pos length : ℕ) :
    (run model buffer pos length).1=BinaryPayload.balancedValue buffer pos length := by
  unfold run BinaryPayload.balancedValue
  split
  · rfl
  · split
    · rfl
    · dsimp only
      have hLow:=value model buffer pos (length/2)
      have hHigh:=value model buffer (pos+length/2) (length-length/2)
      simp only [PlayerSpecificNaturalExecution.binary_value,hLow,hHigh]
      rfl
termination_by length
decreasing_by all_goals omega

theorem bounds (model : RationalCostModel) (buffer : Array Bool) (pos length : ℕ) :
    (run model buffer pos length).1<2^length := by
  rw [value]
  exact BinaryPayload.balancedValue_bounds buffer pos length

end Blotto.PlayerSpecificBalancedPayloadExecution
