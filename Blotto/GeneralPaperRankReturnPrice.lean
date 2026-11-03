import Blotto.GeneralPaperRankArithmetic

/-! Native index intervals bound the raw returned rank, independently of
ordering. The executed child's work/probe metadata is bounded from its exact
native result, so callers supply no metadata-capacity oracle.
-/
namespace Blotto.GeneralPaperRankReturnPrice
open GeneralPaperRankExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem rank_le_hi {n : ℕ} (values : FixedArrayTable n ℕ) (cut depth fuel lo hi : ℕ)
    (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) :
    (GeneralPaperRankSearch.run values cut depth fuel lo hi).rank≤hi := by
  induction fuel generalizing lo hi with
  | zero => exact hOrder
  | succ fuel ih =>
    by_cases hOpen : lo<hi
    · have hm := GeneralPaperRankMidpoint.midpoint_inside n depth lo hi hOpen hHi hSize
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hHi
      rw [GeneralPaperRankSearch.run,ite_eq_left hOpen,dite_eq_left hMid]
      split
      · exact ih _ hi (by omega) hHi
      · exact (ih lo _ hm.1 (by omega)).trans hm.2.le
    · rw [GeneralPaperRankSearch.run,ite_eq_right hOpen]
      exact hOrder

theorem work {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W depth V fuel : ℕ) (values : FixedArrayTable n ℕ) (cut lo hi : ℕ)
    (mid : GeneralPaperRankMidpointPrice.Result) (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth)
    (hFuel : fuel≤depth) (hMid : mid.work=12*depth+2) :
    (finish primitive W (run bits primitive W values cut depth fuel lo hi).1 mid).2≤
      6*primitive (GeneralPaperRankOperands.width depth V)+96*W := by
  apply GeneralPaperRankOperands.finish_work primitive hMono W n depth V fuel _ mid hFuel hSize
  · rw [GeneralPaperRankExecutionData.data bits primitive W values cut depth fuel lo hi hOrder hHi hSize]
    exact GeneralPaperRankSearch.run_work _ _ _ _ _ _
  · rw [GeneralPaperRankExecutionData.data bits primitive W values cut depth fuel lo hi hOrder hHi hSize]
    exact GeneralPaperRankSearch.run_probes _ _ _ _ _ _
  · exact hMid

end Blotto.GeneralPaperRankReturnPrice
