import Blotto.GeneralPaperSummaryOrdered

/-! Compute a rank-search midpoint using only arithmetic and comparisons.
There is no integer-floor primitive or input encoding-length query. The
quotient depth is supplied by the already constructed summary parameters.
-/
namespace Blotto.GeneralPaperRankMidpoint
set_option autoImplicit false
set_option maxHeartbeats 2500000

def midpoint (depth lo hi : ℕ) : GeneralPaperBoundedQuotient.Result :=
  GeneralPaperBoundedQuotient.run ((lo:ℚ)+hi) 2 depth

theorem midpoint_bounds (n depth lo hi : ℕ) (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) :
    2*(midpoint depth lo hi).quotient≤lo+hi ∧ lo+hi<2*((midpoint depth lo hi).quotient+1) := by
  have hn : (n:ℚ)<(2:ℚ)^depth := by exact_mod_cast hSize
  have hl : (lo:ℚ)≤hi := by exact_mod_cast hOrder
  have hh : (hi:ℚ)≤n := by exact_mod_cast hHi
  have hs := GeneralPaperBoundedQuotient.run_spec ((lo:ℚ)+hi) 2 (by norm_num) depth (by positivity) (by linarith)
  have hLow : 2*((midpoint depth lo hi).quotient:ℚ)≤(lo:ℚ)+hi := by
    dsimp only [midpoint]
    linarith only [hs.1,hs.2.1]
  have hHigh : (lo:ℚ)+hi<2*(((midpoint depth lo hi).quotient:ℚ)+1) := by
    dsimp only [midpoint]
    linarith only [hs.1,hs.2.2]
  exact ⟨by exact_mod_cast hLow,by exact_mod_cast hHigh⟩

theorem midpoint_inside (n depth lo hi : ℕ) (hOrder : lo<hi) (hHi : hi≤n) (hSize : n<2^depth) :
    lo≤(midpoint depth lo hi).quotient ∧ (midpoint depth lo hi).quotient<hi := by
  have he := midpoint_bounds n depth lo hi hOrder.le hHi hSize
  omega

theorem midpoint_shrinks (n depth lo hi fuel : ℕ) (hOrder : lo<hi) (hHi : hi≤n)
    (hSize : n<2^depth) (hSpan : hi-lo<2^(fuel+1)) :
    (midpoint depth lo hi).quotient-lo<2^fuel ∧ hi-((midpoint depth lo hi).quotient+1)<2^fuel := by
  have he := midpoint_bounds n depth lo hi hOrder.le hHi hSize
  have hm := midpoint_inside n depth lo hi hOrder hHi hSize
  rw [pow_succ] at hSpan
  omega

theorem midpoint_work (depth lo hi : ℕ) : (midpoint depth lo hi).work=12*depth+2 :=
  GeneralPaperBoundedQuotient.run_work _ _ _

end Blotto.GeneralPaperRankMidpoint
