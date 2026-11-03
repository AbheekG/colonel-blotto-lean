import Blotto.GeneralPaperQuantileOrdering

/-! The native epoch-start summary is already in nondecreasing code order.
No sorting or deduplication is needed to support cached prefix ranks.
-/
namespace Blotto.GeneralPaperSummaryOrdered
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperMassApproximation
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperQuantileComparison
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem search_ordered (lambda k height : ℕ) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (small large : ℕ) (hOrder : small≤large) (hLarge : large≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    (GeneralPaperQuantileSearch.search (prepare lambda k) (width lambda k) small
      (GeneralPaperSourceParameters.prepare k).summarySize height node).location≤
    (GeneralPaperQuantileSearch.search (prepare lambda k) (width lambda k) large
      (GeneralPaperSourceParameters.prepare k).summarySize height node).location := by
  have hm := fresh_bound lambda k 0 node hHeight hValid hPath
  exact GeneralPaperQuantileOrdering.run_ordered lambda k _ hm.1 height node 0 _ zero
    hHeight hValid hPath hm (zero_normal _) small large hOrder hLarge

theorem summary_ordered (lambda k height : ℕ) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    Monotone (GeneralPaperInitialSummary.build (prepare lambda k) (width lambda k)
      (GeneralPaperSourceParameters.prepare k).summarySize height node).read := by
  intro small large hOrder
  rw [GeneralPaperInitialSummary.read_build,GeneralPaperInitialSummary.read_build]
  apply search_ordered lambda k height node hHeight hValid hPath (small.val+1) (large.val+1)
  · have he : small.val≤large.val := hOrder
    omega
  · exact Nat.succ_le_of_lt large.isLt

end Blotto.GeneralPaperSummaryOrdered
