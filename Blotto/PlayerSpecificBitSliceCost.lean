import Blotto.PlayerSpecificBitSliceExecution

/-! Complete operand-sized bit-slice prices, including actual address
arithmetic, every cached bit and the returned finite array/view. -/
namespace Blotto.PlayerSpecificBitSliceCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (M : ℕ) : ℕ := PlayerSpecificResourceBlockReadCost.width M 0
theorem large (M : ℕ) : 32≤width M := (PlayerSpecificResourceBlockReadCost.large M 0).1
theorem word_bound (M n : ℕ) (h : n≤M) : 1+binaryWordWidth n≤width M :=
  PlayerSpecificResourceBlockReadCost.word_bound M 0 n (by unfold PlayerSpecificResourceBlockReadCost.scale; omega)

theorem read_cost (model : RationalCostModel) (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) (j : Fin K) :
    (PlayerSpecificBitSliceExecution.read model M offset K h bits j).2≤100*model.rat (width M) := by
  let W:=width M
  have hj:=j.isLt
  have hoff : offset+j.val≤M := by omega
  have hadd:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a+b) offset j.val W
    (word_bound M offset (by omega)) (word_bound M j.val (by omega)) (word_bound M (offset+j.val) hoff)
  have hw : ∀ word∈[M,K,offset,j.val,offset+j.val],binaryWordWidth word≤W := by
    intro word hword
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hword
    have hn : word≤M := by rcases hword with hword|hword|hword|hword|hword <;> omega
    have hb:=word_bound M word hn
    omega
  have hf:=PlayerSpecificAlgebraicCallerFrame.cost model [] [M,K,offset,j.val,offset+j.val] 0 W
    (by simp) (by simp) hw (by have h:32≤W:=large M; omega) (large M)
  simp only [List.length_nil,List.length_cons,Nat.mul_zero,Nat.zero_add] at hf
  have hR : 1≤model.rat W := (by have h:32≤W:=large M; omega : 1≤W).trans (model.word_le _)
  change (PlayerSpecificNaturalExecution.binary model (fun a b => a+b) offset j.val).2+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] [M,K,offset,j.val,offset+j.val])+2≤100*model.rat W
  omega

theorem profile (K R : ℕ) (hR : 1≤R) : K*(100*R)+2*K+3*(3+K)*R≤120*(K+1)*R := by
  have hm:=Nat.mul_le_mul_left (2*K) hR
  simp only [Nat.mul_one] at hm
  nlinarith only [hm,Nat.zero_le R]

theorem cost (model : RationalCostModel) (M offset K : ℕ) (h : offset+K≤M) (bits : Fin M → Bool) :
    (PlayerSpecificBitSliceExecution.run model M offset K h bits).2≤120*(K+1)*model.rat (width M) := by
  let W:=width M
  let cached:=FixedArrayTable.ofFn (PlayerSpecificBitSliceExecution.read model M offset K h bits)
  have hsum : (∑ j : Fin K,(cached.read j).2)≤K*(100*model.rat W) := by
    have hs:=Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => read_cost model M offset K h bits j)
    simpa only [cached,FixedArrayTable.read_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  have hw : ∀ word∈[M,K,offset]++List.range K,binaryWordWidth word≤W := by
    intro word hword
    have hn : word≤M := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range] at hword
      omega
    have hb:=word_bound M word hn
    omega
  have hf:=PlayerSpecificAlgebraicCallerFrame.cost model [] ([M,K,offset]++List.range K) 0 W
    (by simp) (by simp) hw (by have h:32≤W:=large M; omega) (large M)
  simp only [List.length_nil,List.length_append,List.length_cons,List.length_range,Nat.mul_zero,Nat.zero_add] at hf
  have hR : 1≤model.rat W := (by have h:32≤W:=large M; omega : 1≤W).trans (model.word_le _)
  exact (Nat.add_le_add (Nat.add_le_add_right hsum (2*K)) hf).trans (profile K (model.rat W) hR)

end Blotto.PlayerSpecificBitSliceCost
