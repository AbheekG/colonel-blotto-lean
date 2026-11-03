import Blotto.PlayerSpecificNestedPacketExecution

/-! Complete nested packet source work is polynomial in the original
slot count and precisions, uniformly including empty packets/slices. -/
namespace Blotto.PlayerSpecificNestedPacketSourceCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def size (slots H K : ℕ) : ℕ := slots+H+K+((slots-1)*H+K+K)+10
def coefficient : ℕ := 210*(192^2+192)+2*PlayerSpecificBitSlicePolynomial.coefficient

theorem rational (C S : ℕ) : C*RationalCostModel.schoolbook.rat (PlayerSpecificBitSliceCost.width S)≤
    (C*(192^2+192))*(S+1)^3 := by
  have hw:=RationalCostModel.schoolbook.monotone (PlayerSpecificBitSlicePolynomial.width_bound S)
  have hc:=(Nat.mul_le_mul_left C hw).trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile C 192 (S+1) (by omega))
  exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 1≤S+1) (by decide : 2≤3)))

theorem profile (B C X : ℕ) : (64*B)*X+(64*B)*X+(64*B)*X+C*X+C*X+(18*B)*X=(210*B+2*C)*X := by ring

theorem cost (slots H K : ℕ) (bits : Fin (((slots-1)*H+K)+K) → Bool) :
    (PlayerSpecificNestedPacketExecution.run RationalCostModel.schoolbook slots H K bits).2≤coefficient*(size slots H K+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let S:=size slots H K
  let W:=PlayerSpecificBitSliceCost.width S
  let R:=(slots-1)*H+K
  let M:=R+K
  let headBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) (slots-1) H
  let innerBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) headBits.1 K
  let totalBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) innerBits.1 K
  have hs : slots≤S := by dsimp [S,size]; omega
  have hH : H≤S := by dsimp [S,size]; omega
  have hK : K≤S := by dsimp [S,size]; omega
  have hhead : headBits.1≤S := by change (slots-1)*H≤S; dsimp [S,size]; omega
  have hinner : innerBits.1≤S := by change R≤S; dsimp [R,S,size]; omega
  have htotal : totalBits.1≤S := by change M≤S; dsimp [M,R,S,size]; omega
  have hM : M≤S := htotal
  have hword : ∀ n : ℕ,n≤S → 1+binaryWordWidth n≤W := fun n hn => PlayerSpecificBitSliceCost.word_bound S n hn
  have hm:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a*b) (slots-1) H W
    (hword _ (by omega)) (hword _ hH) (hword _ hhead)
  have hi:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a+b) headBits.1 K W (hword _ hhead) (hword _ hK) (hword _ hinner)
  have ht:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a+b) innerBits.1 K W (hword _ hinner) (hword _ hK) (hword _ htotal)
  have hf:=PlayerSpecificAlgebraicCallerFrame.cost model [] [slots,H,K,headBits.1,innerBits.1,totalBits.1] 0 W
    (by simp) (by simp)
    (by intro n hn
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
        have hn' : n≤S := by rcases hn with hn|hn|hn|hn|hn|hn <;> omega
        have hw:=hword n hn'; omega)
    (by have hw:=PlayerSpecificBitSliceCost.large S; change 32≤W at hw; omega) (PlayerSpecificBitSliceCost.large S)
  change price model (PlayerSpecificNestedPacketExecution.frame slots H K headBits.1 innerBits.1 totalBits.1)≤18*model.rat W at hf
  have hmp:=hm.trans (rational 64 S)
  have hip:=hi.trans (rational 64 S)
  have htp:=ht.trans (rational 64 S)
  have hfp:=hf.trans (rational 18 S)
  have hleft:=PlayerSpecificBitSlicePolynomial.cost M 0 R (by dsimp [M]; omega) bits
  have hright:=PlayerSpecificBitSlicePolynomial.cost M R K (Nat.le_refl _) bits
  have hleft':=hleft.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) 3))
  have hright':=hright.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) 3))
  have hc:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hmp hip) htp) hleft') hright') hfp
  exact hc.trans_eq (profile _ _ _)

end Blotto.PlayerSpecificNestedPacketSourceCost
