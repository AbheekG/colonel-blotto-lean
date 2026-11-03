import Blotto.GeneralPaperLocalEpochControlPrice

/-! Compose one already-priced reached round per loop step. The resulting
bound includes all bounded-buffer and loop-register operations. -/
namespace Blotto.GeneralPaperLocalEpochLoopPrice
open GeneralPaperCatalogueEpochCache GeneralPaperLocalEpochExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem work {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (hMono : Monotone index) (W R : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (capacity count : ℕ)
    (hA : 1≤(if bits then GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2) else W))
    (hIndex : index (1+binaryWordWidth (capacity+1))≤(if bits then GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2) else W))
    (hCount : count≤capacity)
    (hRounds : ∀ time<count,(GeneralPaperRoundExecution.run bits index price W c cache profit T weights Bc Br
      (run bits index price W c cache profit T weights Bc Br first capacity time).1.1).2≤R) :
    (run bits index price W c cache profit T weights Bc Br first capacity count).2≤
      count*(R+256*(if bits then GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2) else W))+
        256*(if bits then GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2) else W) := by
  let A := if bits then GeneralPaperSummaryArrayExecution.arrayWord W (capacity+2) else W
  induction count with
  | zero =>
    simpa only [run, Nat.zero_mul, Nat.zero_add] using
      GeneralPaperLocalEpochControlPrice.initial index hMono A capacity hA hIndex
  | succ count ih =>
    have hp := ih (by omega) (fun time ht => hRounds time (by omega))
    have hr := hRounds count (by omega)
    have hc := GeneralPaperLocalEpochControlPrice.step index hMono A capacity count hA (by omega) hIndex
    rw [run]
    dsimp only
    rw [size]
    dsimp only [A] at hc
    nlinarith only [hp,hr,hc]

end Blotto.GeneralPaperLocalEpochLoopPrice
