import Blotto.PlayerSpecificSegmentDrawSizes

/-! Both actually computed finite-packet counts include operand/result
word work, before any cached prefix or suffix is materialized. -/
namespace Blotto.PlayerSpecificSegmentDrawPacketCost
open PlayerSpecificSegmentDrawSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 512*(192^2+192)

theorem quadratic (C D S : ℕ) (hS : 1≤S) : C*D*(S+1)^2≤(4*C*D)*S^2 := by
  have hp:=Nat.mul_le_mul_left (C*D) (Nat.pow_le_pow_left (show S+1≤2*S by omega) 2)
  exact hp.trans_eq (by ring)

theorem cost (N slots T H K : ℕ) :
    let headBits:=PlayerSpecificNaturalExecution.binary RationalCostModel.schoolbook (fun a b => a*b) (slots-1) H
    let count:=PlayerSpecificNaturalExecution.binary RationalCostModel.schoolbook (fun a b => a+b) headBits.1 K
    headBits.2+count.2≤coefficient*(size N slots T H K)^8 := by
  let model:=RationalCostModel.schoolbook
  let S:=size N slots T H K
  let W:=PlayerSpecificBitSliceCost.width S
  let headBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) (slots-1) H
  let count:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) headBits.1 K
  have hS : 1≤S := by dsimp [S,size]; omega
  have hs : slots-1≤S := by dsimp [S,size]; omega
  have hH : H≤S := by dsimp [S,size]; omega
  have hK : K≤S := by dsimp [S,size]; omega
  have hhead : headBits.1≤S := by change headCount slots H≤S; dsimp [S,size]; omega
  have hcount : count.1≤S := by change packetCount slots H K≤S; dsimp [S,size]; omega
  have hm:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a*b) (slots-1) H W
    (PlayerSpecificBitSliceCost.word_bound S (slots-1) hs) (PlayerSpecificBitSliceCost.word_bound S H hH)
    (PlayerSpecificBitSliceCost.word_bound S headBits.1 hhead)
  have ha:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a+b) headBits.1 K W
    (PlayerSpecificBitSliceCost.word_bound S headBits.1 hhead) (PlayerSpecificBitSliceCost.word_bound S K hK)
    (PlayerSpecificBitSliceCost.word_bound S count.1 hcount)
  change headBits.2≤64*model.rat W at hm
  change count.2≤64*model.rat W at ha
  have hsum : headBits.2+count.2≤128*model.rat W := by omega
  have hw:=model.monotone (PlayerSpecificBitSlicePolynomial.width_bound S)
  have hquad:=PlayerSpecificAlgebraicInverseContract.quadratic_profile 128 192 (S+1) (by omega)
  have hpoly:=((hsum.trans (Nat.mul_le_mul_left 128 hw)).trans hquad).trans (quadratic 128 (192^2+192) S hS)
  exact hpoly.trans (power_transfer coefficient S S 2 (Nat.le_refl _) (by decide) hS)

end Blotto.PlayerSpecificSegmentDrawPacketCost
