import Blotto.GeneralPaperRankOperands

/-! Full primitive-real rank-loop price. The midpoint uses the bounded
arithmetic quotient, including the guarded-read fallback and all native
work/probe/index/control updates. No integer-division primitive is assumed.
-/
namespace Blotto.GeneralPaperRankArithmetic
open GeneralPaperRankExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem control_work (fuel lo hi : ℕ) : GeneralPaperRankExecution.control (fun _ => 1) 1 fuel lo hi=68 := by rfl

theorem finish_work (child : GeneralPaperRankSearch.Result) (mid : GeneralPaperRankMidpointPrice.Result) :
    (finish (fun _ => 1) 1 child mid).2=102 := by rfl

theorem work {n : ℕ} (values : FixedArrayTable n ℕ) (cut depth fuel lo hi : ℕ) :
    (run false (fun _ => 1) 1 values cut depth fuel lo hi).2≤512*(fuel+1)*(depth+1) := by
  induction fuel generalizing lo hi with
  | zero =>
    change 65≤512*(0+1)*(depth+1)
    omega
  | succ fuel ih =>
    rw [run]
    dsimp only
    split
    · rw [GeneralPaperRankMidpointPrice.arithmetic_work,control_work]
      split
      · split
        · rw [finish_work]
          have hi := ih ((GeneralPaperRankMidpointPrice.run false (fun _ => 1) 1 depth lo hi).1.quotient+1) hi
          change 68+(12*depth+82)+1+(1+32)+_+102+2≤512*(fuel+1+1)*(depth+1)
          nlinarith only [hi,Nat.zero_le depth]
        · rw [finish_work]
          have ht := ih lo (GeneralPaperRankMidpointPrice.run false (fun _ => 1) 1 depth lo hi).1.quotient
          change 68+(12*depth+82)+1+(1+32)+_+102≤512*(fuel+1+1)*(depth+1)
          nlinarith only [ht,Nat.zero_le depth]
      · change 68+(12*depth+82)+1+2+64≤512*(fuel+1+1)*(depth+1)
        nlinarith only [Nat.zero_le fuel,Nat.zero_le depth]
    · rw [control_work]
      change 68≤512*(fuel+1+1)*(depth+1)
      nlinarith only [Nat.zero_le fuel,Nat.zero_le depth]

end Blotto.GeneralPaperRankArithmetic
