import Blotto.PlayerSpecificResourceBlockReadCost

/-! Complete fixed fair-block source prices include every cached bit
read, Boolean array/list construction, packet count and caller word. -/
namespace Blotto.PlayerSpecificResourceBlockCost
open PlayerSpecificRationalTrace PlayerSpecificResourceBlockReadCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem block_profile (H R : ℕ) (hR : 1≤R) :
    H*(200*R)+2*H+3*(3+H)*R≤210*(H+1)*R := by
  have hm:=Nat.mul_le_mul_left (2*H) hR
  simp only [Nat.mul_one] at hm
  nlinarith only [hm,Nat.zero_le R]

theorem block_cost (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) (i : Fin fuel) :
    (PlayerSpecificResourceBlockExecution.block model fuel H bits i).2≤210*(H+1)*model.rat (width fuel H) := by
  let W:=width fuel H
  let data:=FixedArrayTable.ofFn (PlayerSpecificResourceBlockExecution.read model fuel H bits i)
  have hsum : (∑ j : Fin H,(data.read j).2)≤H*(200*model.rat W) := by
    have hs:=Finset.sum_le_sum (fun j (_ : j∈(Finset.univ:Finset (Fin H))) => by
      have hc:=PlayerSpecificResourceBlockReadCost.cost model fuel H bits i j
      change (data.read j).2≤200*model.rat W
      rw [FixedArrayTable.read_ofFn]
      exact hc)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  have hw : ∀ word∈[fuel,H,i.val]++List.range H,binaryWordWidth word≤W := by
    intro word hw
    have hsmall : word≤scale fuel H := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (hw|hw|hw)|hw
      · rw [hw]; unfold scale; omega
      · rw [hw]; unfold scale; omega
      · rw [hw]; have hi:=i.isLt; unfold scale; omega
      · have hh:=List.mem_range.mp hw; unfold scale; omega
    have hb:=word_bound fuel H word hsmall
    omega
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model [] ([fuel,H,i.val]++List.range H) 0 W
    (by simp) (by simp) hw (by have h:32≤W:=(large fuel H).1; omega) (large fuel H).1
  simp only [List.length_nil,List.length_append,List.length_cons,List.length_range,Nat.mul_zero,Nat.zero_add] at hframe
  have hR : 1≤model.rat W := (by have h:32≤W:=(large fuel H).1; omega : 1≤W).trans (model.word_le _)
  change (∑ j : Fin H,(data.read j).2)+2*H+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] ([fuel,H,i.val]++List.range H))≤_
  apply le_trans (Nat.add_le_add (Nat.add_le_add_right hsum (2*H)) hframe)
  exact block_profile H (model.rat W) hR

theorem blocks_profile (fuel H R : ℕ) (hR : 1≤R) :
    fuel*(210*(H+1)*R)+64*R+2*fuel+3*(3+fuel)*R≤300*(fuel+1)*(H+1)*R := by
  have hm:=Nat.mul_le_mul_left (2*fuel) hR
  simp only [Nat.mul_one] at hm
  nlinarith only [hm,Nat.zero_le (fuel*H*R),Nat.zero_le (H*R),Nat.zero_le R]

theorem cost (model : RationalCostModel) (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) :
    (PlayerSpecificResourceBlockExecution.blocks model fuel H bits).2≤
      300*(fuel+1)*(H+1)*model.rat (width fuel H) := by
  let W:=width fuel H
  have hsum : ((List.ofFn (PlayerSpecificResourceBlockExecution.block model fuel H bits)).map Prod.snd).sum≤
      fuel*(210*(H+1)*model.rat W) := by
    have hs:=Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin fuel))) => block_cost model fuel H bits i)
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  have hmul:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a*b) fuel H W
    (word_bound fuel H fuel (by unfold scale; omega)) (word_bound fuel H H (by unfold scale; omega))
    (word_bound fuel H (fuel*H) (by unfold scale; omega))
  have hw : ∀ word∈[fuel,H,fuel*H]++List.range fuel,binaryWordWidth word≤W := by
    intro word hw
    have hsmall : word≤scale fuel H := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (hw|hw|hw)|hw
      · rw [hw]; unfold scale; omega
      · rw [hw]; unfold scale; omega
      · rw [hw]; unfold scale; omega
      · have hh:=List.mem_range.mp hw; unfold scale; omega
    have hb:=word_bound fuel H word hsmall
    omega
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model [] ([fuel,H,fuel*H]++List.range fuel) 0 W
    (by simp) (by simp) hw (by have h:32≤W:=(large fuel H).1; omega) (large fuel H).1
  simp only [List.length_nil,List.length_append,List.length_cons,List.length_range,Nat.mul_zero,Nat.zero_add] at hframe
  have hR : 1≤model.rat W := (by have h:32≤W:=(large fuel H).1; omega : 1≤W).trans (model.word_le _)
  change ((List.ofFn (PlayerSpecificResourceBlockExecution.block model fuel H bits)).map Prod.snd).sum+
    (PlayerSpecificNaturalExecution.binary model (fun a b => a*b) fuel H).2+2*fuel+
      price model (PlayerSpecificAlgebraicCallerFrame.run [] ([fuel,H,fuel*H]++List.range fuel))≤_
  apply le_trans (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hsum hmul) (2*fuel)) hframe)
  exact blocks_profile fuel H (model.rat W) hR

end Blotto.PlayerSpecificResourceBlockCost
