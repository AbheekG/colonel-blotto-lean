import Blotto.GeneralPaperQuantileOccurrenceCount
import Blotto.FixedArrayTable

/-! The epoch-start array stores one returned code for each target 1..s.
Its CDF guarantee follows from the actual cached descent. Repeated code
locations occupy distinct array entries and are never deduplicated.
-/
namespace Blotto.GeneralPaperInitialSummary
open scoped BigOperators
open GeneralPaperPreparedPowers GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperQuantileComparison GeneralPaperNormalizedMassError GeneralPaperQuantileSearch
open GeneralPaperQuantileOccurrenceCount GeneralPaperQuantileWork
set_option autoImplicit false
set_option maxHeartbeats 2500000

def build (prepared : Prepared) (width s height : ℕ) (node : Node height) : FixedArrayTable s ℕ :=
  FixedArrayTable.ofFn (fun r => (search prepared width (r.val+1) s height node).location)

def work (prepared : Prepared) (width s height : ℕ) (node : Node height) : ℕ :=
  (∑ r : Fin s, (search prepared width (r.val+1) s height node).work)+8*s+16

theorem read_build (prepared : Prepared) (width s height : ℕ) (node : Node height) (r : Fin s) :
    (build prepared width s height node).read r=(search prepared width (r.val+1) s height node).location :=
  FixedArrayTable.read_ofFn _ _

theorem code_bounds (prepared : Prepared) (width s height : ℕ) (node : Node height) (r : Fin s) :
    (build prepared width s height node).read r<2^height := by
  rw [read_build]
  exact location_bound _ _ _ _ _ _

theorem targets (lambda k height : ℕ) (node : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    cdf k node ((build (prepare lambda k) (width lambda k) (GeneralPaperSourceParameters.prepare k).summarySize height node).read r)≤
      ((r.val:ℚ)+1)/(GeneralPaperSourceParameters.prepare k).summarySize+delta k ∧
    ((r.val:ℚ)+1)/(GeneralPaperSourceParameters.prepare k).summarySize-delta k≤
      cdf k node ((build (prepare lambda k) (width lambda k) (GeneralPaperSourceParameters.prepare k).summarySize height node).read r+1) := by
  simpa only [read_build,Nat.cast_add,Nat.cast_one] using
    search_bracket lambda k (r.val+1) height node (Nat.succ_le_of_lt r.isLt) hHeight hValid hPath

theorem cdf_error (lambda k height : ℕ) (node : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (cut : ℕ) (hCut : cut≤2^height) :
    |summaryCDF (build (prepare lambda k) (width lambda k)
      (GeneralPaperSourceParameters.prepare k).summarySize height node).read cut-cdf k node cut|<
      (GeneralPaperSourceParameters.prepare k).nu := by
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  have he := quantile_discrepancy hs _ (cdf k node) (delta k) (delta_nonnegative k)
    (cdf_monotone k node) (cdf_zero k node) (cdf_total k node)
    (targets lambda k height node hHeight hValid hPath) cut hCut
  exact he.trans_lt (summary_slack k)

theorem build_work (lambda k width s height : ℕ) (node : Node height) :
    work (prepare lambda k) width s height node≤
      s*(massPrice lambda k+height*(stepPrice lambda k width+8)+32)+16 := by
  have he := Finset.sum_le_sum (fun (r : Fin s) (_ : r∈Finset.univ) => search_work lambda k width (r.val+1) s height node)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at he
  unfold work
  nlinarith

end Blotto.GeneralPaperInitialSummary
