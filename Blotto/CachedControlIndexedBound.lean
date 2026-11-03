import Blotto.CachedControlPrices

/-! Boolean encoding/coin-body allowances hold at arbitrary indexed reader
positions. Reached word heights and a closed invariant leave the production
words and cap unchanged; remaining-bit visits are charged explicitly. -/

namespace Blotto.WordTransition

theorem wordsHeight_tracked {S α : Type*} (t : WordTransition S α) (limit : ℕ) (h : t.WordsHeight limit) :
    t.TrackedWordsHeight (fun _ => true) limit := by
  cases t with
  | done value => trivial
  | ask a b hb hab upper lower => exact fun _ => h

end Blotto.WordTransition
namespace Blotto.WordStateMachine

theorem cachedControlWork_state_bound_under {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (C : ℕ) (hRank : m.rank state ≤ C)
    (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedControlWork (fun _ => true) (fun w => 4 * w) FixedWordCoin.bodyAllowance
      N bits (.state state) pos hpos ≤
      4 * limit * C + (24 * limit + 28) * (2 * C + 2 * (N - pos) + 2) := by
  have hPath := m.runCachedIndexed_trackedWordsBounded I (fun _ => true) limit
    (fun s hs => WordTransition.wordsHeight_tracked _ limit (hWords s hs)) hClosed
    N bits (.state state) pos hpos hI
  have hEnc := m.cachedTrackedEncodingCells_requests I (fun _ => true) limit N bits (.state state) pos hpos hPath
  have hReq := m.cachedRequests_bound N bits (.state state) pos hpos
  change m.cachedRequests N bits (.state state) pos hpos ≤ m.rank state at hReq
  have hEncoding := hEnc.trans (Nat.mul_le_mul_left (2 * limit) (hReq.trans hRank))
  have hWord := m.cachedTrackedWordWork_visits I (fun _ => true) limit N bits (.state state) pos hpos hPath
  rw [FixedWordCoin.bodyAllowance_eq, m.cachedCounts_refines] at hWord
  have hVisits := (m.indexedCounts_bounds N bits (.state state) pos hpos).2
  change (m.indexedCounts N bits (.state state) pos hpos).visits ≤ 2 * m.rank state + 1 + 2 * (N - pos) + 1 at hVisits
  have hVisitsC : (m.indexedCounts N bits (.state state) pos hpos).visits ≤ 2 * C + 2 * (N - pos) + 2 := by omega
  have hBody := hWord.trans (Nat.mul_le_mul_left (24 * limit + 28) hVisitsC)
  rw [m.cachedControlWork_prices_refine]
  nlinarith

end Blotto.WordStateMachine
