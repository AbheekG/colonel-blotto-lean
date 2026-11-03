import Blotto.GeneralPaperTypedDecodeExecution

/-! Full backtracking work including unsuccessful branches and actual
reference-list concatenation. The bound uses the balanced typed height,
with no list-length pass or reconstructed DP computation. -/
namespace Blotto.GeneralPaperTypedDecodePrice
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem combine (A h left right : ℕ) (hl : left≤256*2^h*(h+1)*A) (hr : right≤256*2^h*(h+1)*A) :
    left+right+(8*A*2^h+130*A)≤256*2^(h+1)*(h+2)*A := by
  have hp : 1≤2^h := Nat.one_le_two_pow
  have ha := Nat.mul_le_mul_right A hp
  rw [pow_succ]
  nlinarith only [hl,hr,ha,Nat.zero_le (2^h*A)]

theorem work {K J h : ℕ} (A : ℕ) (computed : Computation Tag K J h) (label : Fin J) :
    (GeneralPaperTypedDecodeExecution.run A computed label).2≤256*2^h*(h+1)*A := by
  induction computed generalizing label with
  | leaf states =>
    cases hs : states.read label <;> simp only [GeneralPaperTypedDecodeExecution.run,hs] <;> omega
  | @node h left right states ihl ihr =>
    cases hs : states.read label with
    | none =>
      have hc := combine A h 0 0 (Nat.zero_le _) (Nat.zero_le _)
      simp only [GeneralPaperTypedDecodeExecution.run,hs]
      nlinarith only [hc,Nat.zero_le (A*2^h)]
    | some chosen =>
      have hl := ihl chosen.predecessor.1
      cases hLeft : (GeneralPaperTypedDecodeExecution.run A left chosen.predecessor.1).1 with
      | none =>
        have hc := combine A h _ 0 hl (Nat.zero_le _)
        simp only [GeneralPaperTypedDecodeExecution.run,hs,hLeft]
        nlinarith only [hc,Nat.zero_le (A*2^h)]
      | some ll =>
        have hr := ihr chosen.predecessor.2
        have hc := combine A h _ _ hl hr
        cases hRight : (GeneralPaperTypedDecodeExecution.run A right chosen.predecessor.2).1 with
        | none =>
          simp only [GeneralPaperTypedDecodeExecution.run,hs,hLeft,hRight]
          nlinarith only [hc,Nat.zero_le (A*2^h)]
        | some rr =>
          have hLen := GeneralPaperTypedDecodeExecution.length A left chosen.predecessor.1 ll hLeft
          have ha := GeneralPaperPricedListAppend.work A ll rr
          rw [hLen] at ha
          simp only [GeneralPaperTypedDecodeExecution.run,hs,hLeft,hRight]
          rw [ha]
          nlinarith only [hc]

end Blotto.GeneralPaperTypedDecodePrice
