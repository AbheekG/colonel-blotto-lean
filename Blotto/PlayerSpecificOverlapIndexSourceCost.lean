import Blotto.PlayerSpecificOverlapIndexExecution

/-! Product-slot decoding has a complete polynomial source price
from the original dimensions, including empty-product domains. -/
namespace Blotto.PlayerSpecificOverlapIndexSourceCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (k h : ℕ) : ℕ := (146*(192^2+192))*(k+h+k*h+3)^3
theorem profile (R : ℕ) : 64*R+64*R+18*R=146*R := by ring

theorem cost (k h : ℕ) (slot : Fin (k*h)) :
    (PlayerSpecificOverlapIndexExecution.run RationalCostModel.schoolbook k h slot).2≤work k h := by
  let model:=RationalCostModel.schoolbook
  let S:=k+h+k*h+2
  let W:=PlayerSpecificBitSliceCost.width S
  let quotient:=PlayerSpecificNaturalExecution.binary model (fun a b => a/b) slot.val h
  let remainder:=PlayerSpecificNaturalExecution.binary model (fun a b => a%b) slot.val h
  have hk : k≤S := by dsimp [S]; omega
  have hh : h≤S := by dsimp [S]; omega
  have hs : slot.val≤S := by have hj:=slot.isLt; dsimp [S]; omega
  have hq : quotient.1≤S := by
    have hj:=(finProdFinEquiv.symm slot).1.isLt
    change slot.val/h<k at hj
    change slot.val/h≤S
    omega
  have hr : remainder.1≤S := by
    have hj:=(finProdFinEquiv.symm slot).2.isLt
    change slot.val%h<h at hj
    change slot.val%h≤S
    omega
  have hword : ∀ n : ℕ,n≤S → 1+binaryWordWidth n≤W := fun n hn => PlayerSpecificBitSliceCost.word_bound S n hn
  have hdiv:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a/b) slot.val h W (hword _ hs) (hword _ hh) (hword _ hq)
  have hmod:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a%b) slot.val h W (hword _ hs) (hword _ hh) (hword _ hr)
  have hf:=PlayerSpecificAlgebraicCallerFrame.cost model [] [k,h,slot.val,quotient.1,remainder.1,1] 0 W
    (by simp) (by simp)
    (by intro n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        have hn' : n≤S := by rcases hn with hn|hn|hn|hn|hn|hn <;> dsimp [S] at * <;> omega
        have hw:=hword n hn'; omega)
    (by have hw:=PlayerSpecificBitSliceCost.large S; change 32≤W at hw; omega) (PlayerSpecificBitSliceCost.large S)
  change price model (PlayerSpecificOverlapIndexExecution.frame k h slot.val quotient.1 remainder.1)≤18*model.rat W at hf
  have hc:=(Nat.add_le_add (Nat.add_le_add hdiv hmod) hf).trans_eq (profile _)
  exact hc.trans (PlayerSpecificNestedPacketSourceCost.rational 146 S)

end Blotto.PlayerSpecificOverlapIndexSourceCost
