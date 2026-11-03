import Blotto.PlayerSpecificNestedTerminalDrawSourceCost

/-! Actual product-slot decoding retains its quotient and remainder
once and prices both natural operations and all finite index words. -/
namespace Blotto.PlayerSpecificOverlapIndexExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (k h slot quotient remainder : ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [] [k,h,slot,quotient,remainder,1]
def run (model : RationalCostModel) (k h : ℕ) (slot : Fin (k*h)) : (Fin k×Fin h)×ℕ :=
  let quotient:=PlayerSpecificNaturalExecution.binary model (fun a b => a/b) slot.val h
  let remainder:=PlayerSpecificNaturalExecution.binary model (fun a b => a%b) slot.val h
  let first:Fin k:=⟨quotient.1,by change slot.val/h<k; exact (finProdFinEquiv.symm slot).1.isLt⟩
  let second:Fin h:=⟨remainder.1,by change slot.val%h<h; exact (finProdFinEquiv.symm slot).2.isLt⟩
  ((first,second),quotient.2+remainder.2+price model (frame k h slot.val quotient.1 remainder.1))

theorem value (model : RationalCostModel) (k h : ℕ) (slot : Fin (k*h)) :
    (run model k h slot).1=finProdFinEquiv.symm slot := by
  apply Prod.ext
  · apply Fin.ext; rfl
  · apply Fin.ext; rfl

end Blotto.PlayerSpecificOverlapIndexExecution
