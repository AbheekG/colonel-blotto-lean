import Blotto.GeneralPaperRankExecution

/-! Constructed rank states exclude the guarded-read fallback. The selected
branch preserves its closed index interval; ordering is needed for the rank
specification, but not for exact equality of the two executable results.
-/
namespace Blotto.GeneralPaperRankExecutionData
open GeneralPaperRankExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem data {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (W : ℕ) (values : FixedArrayTable n ℕ)
    (cut depth fuel lo hi : ℕ) (hOrder : lo≤hi) (hHi : hi≤n) (hSize : n<2^depth) :
    (run bits primitive W values cut depth fuel lo hi).1=GeneralPaperRankSearch.run values cut depth fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    rw [run,GeneralPaperRankSearch.run]
    dsimp only
    split
    · rename_i hOpen
      have hm := GeneralPaperRankMidpoint.midpoint_inside n depth lo hi hOpen hHi hSize
      have hMid : (GeneralPaperRankMidpoint.midpoint depth lo hi).quotient<n := hm.2.trans_le hHi
      have hd := GeneralPaperRankMidpointPrice.data bits primitive W n depth lo hi hOrder hHi hSize
      simp only [hd,GeneralPaperRankMidpointPrice.specification]
      simp only [hMid,dite_eq_left]
      split
      · simp only [finish]
        rw [ih _ hi (by omega) hHi]
      · simp only [finish]
        rw [ih lo _ hm.1 (by omega)]
    · rfl

end Blotto.GeneralPaperRankExecutionData
