import Blotto.GeneralPaperBalancedTagPrice

/-! Separate fixed non-resource work from the exact balanced resource
price. Aggregating the latter uses the model's own superadditivity. The
bound retains one Rat of the actual all-level word total. -/
namespace Blotto.GeneralPaperOrderedDPAggregatePrice
open GeneralPaperTagHeight
set_option autoImplicit false
set_option maxHeartbeats 5000000

def leafBase (price : ℕ → ℕ) (W m lambda k Qv K J : ℕ) : ℕ :=
  GeneralPaperDPTableControls.emptyProfile W J+GeneralPaperDPTableControls.labelsProfile W K+
    K*(GeneralPaperCachedProfitGridPrice.profile price W m lambda k Qv+384*W+
      128*GeneralPaperSummaryArrayExecution.arrayWord W J)+320*W

def mergeBase (price : ℕ → ℕ) (W m lambda k Qv J : ℕ) : ℕ :=
  GeneralPaperDPTableControls.emptyProfile W J+GeneralPaperDPTableControls.labelsProfile W J+
    J*(J*(GeneralPaperCachedProfitGridPrice.profile price W m lambda k Qv+
      2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+576*W+
      256*GeneralPaperSummaryArrayExecution.arrayWord W J)+128*W)+320*W

theorem zero (price : ℕ → ℕ) (W m lambda k Qv K J s : ℕ) :
    GeneralPaperOrderedDPPrice.bitProfile price W m lambda k Qv K J s 0=
      leafBase price W m lambda k Qv K J+2*K*price (word s 0) := by
  rw [GeneralPaperOrderedDPPrice.bitProfile,word_zero]
  unfold GeneralPaperOrderedTablePrice.leafProfile GeneralPaperOrderedScatterPrice.entryProfile leafBase
  ring

theorem succ (price : ℕ → ℕ) (W m lambda k Qv K J s h : ℕ) :
    GeneralPaperOrderedDPPrice.bitProfile price W m lambda k Qv K J s (h+1)=
      2*GeneralPaperOrderedDPPrice.bitProfile price W m lambda k Qv K J s h+
      mergeBase price W m lambda k Qv J+4*J^2*price (word s (h+1)) := by
  rw [GeneralPaperOrderedDPPrice.bitProfile]
  unfold GeneralPaperOrderedTablePrice.mergeProfile GeneralPaperOrderedMergeEntryPrice.profile
    GeneralPaperOrderedScatterPrice.entryProfile mergeBase word
  ring

theorem balanced (price : ℕ → ℕ) (W m lambda k Qv K J s H : ℕ) :
    GeneralPaperOrderedDPPrice.bitProfile price W m lambda k Qv K J s H+mergeBase price W m lambda k Qv J≤
      2^H*(leafBase price W m lambda k Qv K J+mergeBase price W m lambda k Qv J)+
        (2*K+4*J^2)*GeneralPaperBalancedTagWords.profile price s H := by
  induction H with
  | zero =>
    rw [zero,GeneralPaperBalancedTagPrice.profile_zero,pow_zero,one_mul]
    nlinarith only [Nat.zero_le (4*J^2*price (word s 0))]
  | succ H ih =>
    rw [succ,GeneralPaperBalancedTagPrice.profile_succ,pow_succ (2:ℕ) H]
    nlinarith only [ih,Nat.zero_le (2*K*price (word s (H+1)))]

def profile (model : RationalCostModel) (W m lambda k Qv K J s H : ℕ) : ℕ :=
  2^H*(leafBase model.rat W m lambda k Qv K J+mergeBase model.rat W m lambda k Qv J)+
    (2*K+4*J^2)*model.rat ((H+1)*2^H*(2*s+2))

theorem bound (model : RationalCostModel) (W m lambda k Qv K J s H : ℕ) :
    GeneralPaperOrderedDPPrice.bitProfile model.rat W m lambda k Qv K J s H≤profile model W m lambda k Qv K J s H := by
  have hb := balanced model.rat W m lambda k Qv K J s H
  have ha := Nat.mul_le_mul_left (2*K+4*J^2) (GeneralPaperBalancedTagPrice.aggregate model s H)
  unfold profile
  omega

theorem work {K h : ℕ} (model : RationalCostModel) (W m lambda k Qv s : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (tree : GeneralPaperOrderedProfitDP.Tree GeneralPaperResponseTag.Tag K h)
    (hl : GeneralPaperOrderedDPHeight.Leaves s tree)
    (hNum : GeneralPaperOrderedDPProfitCaps.Leaves (2*prepared.parameters.qProf) tree) :
    (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).2≤
      profile model W m lambda k Qv K prepared.grid.size s h :=
  (GeneralPaperOrderedDPPrice.bit_work model.rat model.monotone W m lambda k Qv s prepared hp tree hl hNum).trans
    (bound model W m lambda k Qv K prepared.grid.size s h)

end Blotto.GeneralPaperOrderedDPAggregatePrice
