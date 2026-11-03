import Blotto.GeneralPaperSignedUpdatePrice

/-! Combine one complete CDF-pair plan and one complete signed-tail plan.
Both native work additions and the final plan record are explicitly priced.
-/
namespace Blotto.GeneralPaperQueryLossExecution
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary tailSummary : Summary k)
    (queries : FixedArrayTable m ℕ) : GeneralPaperQueryLossCounts.Plan k m × ℕ :=
  let cdf := GeneralPaperCDFPairExecution.run bits index price W k cdfSummary queries
  let tails := GeneralPaperSignedTailExecution.run bits index price W k U tailSummary queries
  (⟨cdf.1,tails.1,cdf.1.work+tails.1.work+16⟩,
    cdf.2+tails.2+GeneralPaperFieldPlanCounters.pair price cdf.1.work tails.1.work+128*W)

theorem data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary tailSummary : Summary k)
    (queries : FixedArrayTable m ℕ) :
    (run bits index price W k U cdfSummary tailSummary queries).1=GeneralPaperQueryLossCounts.prepare k U cdfSummary tailSummary queries := by
  unfold run GeneralPaperQueryLossCounts.prepare
  dsimp only
  simp only [GeneralPaperCDFPairExecution.data,GeneralPaperSignedTailExecution.data]

end Blotto.GeneralPaperQueryLossExecution
