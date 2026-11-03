import Blotto.PlayerSpecificBalancedPayloadMergeCost

/-! The complete native balanced decoder has at most 2*K+1 executing
nodes, with bounded natural arithmetic, arrays, indices and returned words. -/
namespace Blotto.PlayerSpecificBalancedPayloadCost
open PlayerSpecificBalancedPayloadExecution PlayerSpecificBalancedPayloadBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def nodes (length : ℕ) : ℕ := if length=0 then 1 else 2*length-1

theorem nodes_split (length : ℕ) (h : 1<length) :
    nodes (length/2)+nodes (length-length/2)+1=nodes length := by
  have hl : length/2≠0 := by omega
  have hh : length-length/2≠0 := by omega
  simp only [nodes,hl,hh,show length≠0 by omega,ite_false]
  omega

theorem cost (model : RationalCostModel) (buffer : Array Bool) (S : ℕ) (hb : buffer.size≤S)
    (pos length : ℕ) (hp : pos+length≤S) :
    (run model buffer pos length).2≤nodes length*400*model.rat (width S) := by
  unfold run
  split
  · rename_i hz
    have hc:=frame_cost model buffer pos length 0 S hb (by omega) (by omega) (small_word 0 S (by omega))
    have hn : nodes length=1 := by rw [hz]; rfl
    rw [hn]
    exact hc.trans (Nat.mul_le_mul_right _ (by decide : 13≤1*400))
  · rename_i hn
    split
    · rename_i hOne
      let result:=if buffer.getD pos false then 1 else 0
      have hr : binaryWordWidth result≤S+1 := small_word result S (by dsimp only [result]; split <;> omega)
      have hc:=frame_cost model buffer pos length result S hb (by omega) (by omega) hr
      have hnodes : nodes length=1 := by rw [hOne]; rfl
      rw [hnodes]
      exact hc.trans (Nat.mul_le_mul_right _ (by decide : 13≤1*400))
    · rename_i hOne
      have hLength : 1<length := by omega
      have hlow:=cost model buffer S hb pos (length/2) (by omega)
      have hhigh:=cost model buffer S hb (pos+length/2) (length-length/2) (by omega)
      have hmerge:=PlayerSpecificBalancedPayloadMergeCost.cost model buffer pos length S hb hp hLength
      have hnodes:=nodes_split length hLength
      dsimp only
      simp only [PlayerSpecificNaturalExecution.binary_value]
      dsimp only at hmerge
      have hm:=Nat.mul_le_mul_right (400*model.rat (width S)) (le_of_eq hnodes)
      nlinarith only [hlow,hhigh,hmerge,hm]
termination_by length
decreasing_by all_goals omega

theorem polynomial_cost (model : RationalCostModel) (buffer : Array Bool) (pos length : ℕ) :
    (run model buffer pos length).2≤(2*length+1)*400*model.rat (width (buffer.size+pos+length)) := by
  have hc:=cost model buffer (buffer.size+pos+length) (by omega) pos length (by omega)
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat (width (buffer.size+pos+length)))
  apply Nat.mul_le_mul_right 400
  unfold nodes
  split <;> omega

end Blotto.PlayerSpecificBalancedPayloadCost
