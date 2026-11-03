import Blotto.GeneralPaperPrecallWordEnvelope

/-! Constant-register traversal of the constructed divisor powers.
Ascend by doubling and then descend by exact halving. Neither tail loop
retains a list of the intermediate divisors. Data/price/space joins follow.
-/
namespace Blotto.GeneralPaperQuotientTraversal
set_option autoImplicit false
set_option maxHeartbeats 6000000

structure Top where
  scale : ℕ
  depth : ℕ

def up (n scale : ℕ) : ℕ → ℕ → Top
  | 0,count => ⟨scale,count⟩
  | fuel+1,count => if n<scale then ⟨scale,count⟩ else up n (2*scale) fuel (count+1)

def restore (scale : ℕ) (qr : ℕ × ℕ) : ℕ × ℕ :=
  if scale≤qr.2 then (2*qr.1+1,qr.2-scale) else (2*qr.1,qr.2)

def down (scale : ℕ) : ℕ → (ℕ × ℕ) → ℕ × ℕ
  | 0,qr => qr
  | remaining+1,qr =>
    let smaller := scale/2
    down smaller remaining (restore smaller qr)

theorem halve (a depth : ℕ) : (a*2^(depth+1))/2=a*2^depth := by
  rw [pow_succ,←Nat.mul_assoc,Nat.mul_comm (a*2^depth) 2]
  exact Nat.mul_div_cancel_left _ (by decide : 0<(2:ℕ))

theorem down_last (a depth : ℕ) (qr : ℕ × ℕ) :
    down (a*2^(depth+1)) (depth+1) qr=restore a (down (a*2^(depth+1)) depth qr) := by
  induction depth generalizing qr with
  | zero => simp only [down,halve,pow_zero,Nat.mul_one]
  | succ depth ih =>
    rw [down,halve,ih]
    rw [down,halve]

theorem up_data (n a fuel count : ℕ) :
    let native := GeneralPaperNaturalGrowingQuotient.run n a fuel
    (up n a fuel count).scale=a*2^native.depth ∧ (up n a fuel count).depth=count+native.depth := by
  induction fuel generalizing a count with
  | zero => simp only [up,GeneralPaperNaturalGrowingQuotient.run,pow_zero,Nat.mul_one,Nat.add_zero,and_self]
  | succ fuel ih =>
    rw [up,GeneralPaperNaturalGrowingQuotient.run]
    split
    · simp only [pow_zero,Nat.mul_one,Nat.add_zero,and_self]
    · have hi := ih (2*a) (count+1)
      dsimp only
      split
      · dsimp only
        rw [pow_succ]
        exact ⟨by nlinarith only [hi.1],by omega⟩
      · dsimp only
        rw [pow_succ]
        exact ⟨by nlinarith only [hi.1],by omega⟩

end Blotto.GeneralPaperQuotientTraversal
