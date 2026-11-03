import Blotto.PlayerSpecificBalancedPayloadBounds

/-! All five natural operations and the enclosing buffer/return caller
of one actual balanced merge have a derived common source-price bound. -/
namespace Blotto.PlayerSpecificBalancedPayloadMergeCost
open PlayerSpecificBalancedPayloadExecution PlayerSpecificBalancedPayloadBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost (model : RationalCostModel) (buffer : Array Bool) (pos length S : ℕ)
    (hb : buffer.size≤S) (hp : pos+length≤S) (hlen : 1<length) :
    let low:=length/2
    let high:=length-low
    let lower:=(run model buffer pos low).1
    let upper:=(run model buffer (pos+low) high).1
    let shifted:=Nat.shiftLeft upper low
    (PlayerSpecificNaturalExecution.binary model (fun a b => a/b) length 2).2+
      (PlayerSpecificNaturalExecution.binary model (fun a b => a-b) length low).2+
      (PlayerSpecificNaturalExecution.binary model (fun a b => a+b) pos low).2+
      (PlayerSpecificNaturalExecution.binary model Nat.shiftLeft upper low).2+
      (PlayerSpecificNaturalExecution.binary model (fun a b => a+b) lower shifted).2+
      frame model buffer pos length (lower+shifted)≤400*model.rat (width S) := by
  let low:=length/2
  let high:=length-low
  let lower:=(run model buffer pos low).1
  let upper:=(run model buffer (pos+low) high).1
  let shifted:=Nat.shiftLeft upper low
  have hl : length≤S := by omega
  have hpos : pos≤S := by omega
  have hlow : low≤S := by dsimp [low]; omega
  have hhigh : high≤S := by dsimp [high,low]; omega
  have hhighpos : pos+low≤S := by dsimp [low]; omega
  have h2 : binaryWordWidth 2≤S+1 := by
    have h2:binaryWordWidth 2=2 := by decide
    rw [h2]
    omega
  have hlw:=small_word length S hl
  have hloww:=small_word low S hlow
  have hhighw:=small_word high S hhigh
  have hposw:=small_word pos S hpos
  have hhighposw:=small_word (pos+low) S hhighpos
  have hlower : binaryWordWidth lower≤S+1 := result_width model buffer pos low S hlow
  have hupper : binaryWordWidth upper≤S+1 := result_width model buffer (pos+low) high S hhigh
  have hshift : binaryWordWidth shifted≤S+1 := by
    apply binaryWordWidth_le_of_lt_pow (by omega)
    exact (shifted_bound model buffer pos length).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hout : binaryWordWidth (lower+shifted)≤S+1 := by
    apply binaryWordWidth_le_of_lt_pow (by omega)
    exact (added_bound model buffer pos length hlen).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hdiv:=binary_cost model (fun a b => a/b) length 2 S hlw h2 hloww
  have hsub:=binary_cost model (fun a b => a-b) length low S hlw hloww hhighw
  have haddPos:=binary_cost model (fun a b => a+b) pos low S hposw hloww hhighposw
  have hshiftCost:=binary_cost model Nat.shiftLeft upper low S hupper hloww hshift
  have hadd:=binary_cost model (fun a b => a+b) lower shifted S hlower hshift hout
  have hframe:=frame_cost model buffer pos length (lower+shifted) S hb hpos hl hout
  dsimp only [low,high,lower,upper,shifted] at hdiv hsub haddPos hshiftCost hadd hframe ⊢
  omega

end Blotto.PlayerSpecificBalancedPayloadMergeCost
