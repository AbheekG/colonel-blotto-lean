import Blotto.PlayerSpecificResourceBlockExecution

/-! Every actual fair-packet read includes its computed multiplication,
offset, source index/control words and Boolean read/write work. -/
namespace Blotto.PlayerSpecificResourceBlockReadCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scale (fuel H : ℕ) : ℕ := fuel*H+fuel+H+2
def width (fuel H : ℕ) : ℕ := 64*(scale fuel H+1)

theorem large (fuel H : ℕ) : 32≤width fuel H ∧ scale fuel H+2≤width fuel H := by
  unfold width scale
  omega

theorem word_bound (fuel H n : ℕ) (hn : n≤scale fuel H) : 1+binaryWordWidth n≤width fuel H := by
  have hw:=(control_width n).trans (Nat.add_le_add_right hn 1)
  exact (by omega : 1+binaryWordWidth n≤scale fuel H+2).trans (large fuel H).2

theorem cost (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) (i : Fin fuel) (j : Fin H) :
    (PlayerSpecificResourceBlockExecution.read model fuel H bits i j).2≤200*model.rat (width fuel H) := by
  let W:=width fuel H
  have hbase : i.val*H≤fuel*H := Nat.mul_le_mul_right H (Nat.le_of_lt i.isLt)
  have hoff : i.val*H+j.val≤fuel*H := (PlayerSpecificResourceBlockExecution.address fuel H i j).isLt.le
  have hfuel : fuel≤scale fuel H := by unfold scale; omega
  have hH : H≤scale fuel H := by unfold scale; omega
  have hi : i.val≤scale fuel H := (Nat.le_of_lt i.isLt).trans hfuel
  have hj : j.val≤scale fuel H := (Nat.le_of_lt j.isLt).trans hH
  have hprod : i.val*H≤scale fuel H := by unfold scale; omega
  have hsum : i.val*H+j.val≤scale fuel H := by unfold scale; omega
  have hmul:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a*b) i.val H W
    (word_bound fuel H i.val hi) (word_bound fuel H H hH) (word_bound fuel H (i.val*H) hprod)
  have hadd:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a+b) (i.val*H) j.val W
    (word_bound fuel H (i.val*H) hprod) (word_bound fuel H j.val hj) (word_bound fuel H (i.val*H+j.val) hsum)
  have hwords : ∀ word∈[fuel,H,i.val,j.val,i.val*H+j.val],binaryWordWidth word≤W := by
    intro word hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    have hn : word≤scale fuel H := by rcases hw with hw|hw|hw|hw|hw <;> omega
    have h:=word_bound fuel H word hn
    omega
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model [] [fuel,H,i.val,j.val,i.val*H+j.val] 0 W
    (by simp) (by simp) hwords (by have h:32≤W:=(large fuel H).1; omega) (large fuel H).1
  simp only [List.length_nil,List.length_cons,Nat.mul_zero,Nat.zero_add] at hframe
  have hR : 1≤model.rat W := (by have h:32≤W:=(large fuel H).1; omega : 1≤W).trans (model.word_le _)
  change (PlayerSpecificNaturalExecution.binary model (fun a b => a*b) i.val H).2+
    (PlayerSpecificNaturalExecution.binary model (fun a b => a+b) (i.val*H) j.val).2+
      price model (PlayerSpecificAlgebraicCallerFrame.run [] [fuel,H,i.val,j.val,i.val*H+j.val])+2≤_
  change _≤200*model.rat W
  omega

end Blotto.PlayerSpecificResourceBlockReadCost
