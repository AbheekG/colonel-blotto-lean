import Blotto.CachedWordControllerCounts
import Blotto.WordMachineWordHeight

/-! Actual cached word widths follow the Boolean production path. Each new
request uses its denominator's minimal word width; pending steps retain it.
All visited states preserve the supplied source invariant, including caps. -/

namespace Blotto.CachedWordCursor

def Bounded {S : Type*} (I : S → Prop) (limit : ℕ) : CachedWordCursor S → Prop
  | .state s => I s
  | @CachedWordCursor.coin _ w _ _ _ _ upper lower => w ≤ limit ∧ I upper ∧ I lower

theorem ofWords_bounded {S : Type*} (I : S → Prop) (limit a b : ℕ) (hb : 0 < b)
    (hab : a ≤ b) (hB : b < 2 ^ limit) (upper lower : S) (hUpper : I upper) (hLower : I lower) :
    (ofWords a b hb hab upper lower).Bounded I limit := by
  have hLog := (Nat.log2_lt (ne_of_gt hb)).mpr hB
  change binaryWordWidth b ≤ limit ∧ I upper ∧ I lower
  unfold binaryWordWidth
  exact ⟨by omega, hUpper, hLower⟩

end Blotto.CachedWordCursor
namespace Blotto.WordStateMachine

def CachedWordsBounded {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (limit N : ℕ)
    (bits : Fin N → Bool) (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : Prop :=
  match cursor with
  | .state s => I s ∧ match _hs : m.step s with
    | .done _ => True
    | .ask a b hb hab upper lower =>
      m.CachedWordsBounded I limit N bits (.ofWords a b hb hab upper lower) pos hpos
  | @CachedWordCursor.coin _ w a b hb hab upper lower =>
    w ≤ limit ∧ if hz : a.isZero = true then m.CachedWordsBounded I limit N bits (.state lower) pos hpos else
      if he : a.same b = true then m.CachedWordsBounded I limit N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            m.CachedWordsBounded I limit N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.CachedWordsBounded I limit N bits (.state (if bits ⟨pos, hRead⟩ then lower else upper))
            (pos + 1) (by omega)
        else True
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCachedIndexed_wordsBounded {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True)) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) (hCursor : cursor.Bounded I limit) :
    m.CachedWordsBounded I limit N bits cursor pos hpos := by
  cases hCursorEq : cursor with
  | state s =>
    rw [hCursorEq] at hCursor
    unfold CachedWordsBounded
    refine ⟨hCursor, ?_⟩
    cases hs : m.step s with
    | done value => trivial
    | ask a b hb hab upper lower =>
      have hw := hWords s hCursor
      have hc := hClosed s hCursor
      rw [hs] at hw hc
      exact m.runCachedIndexed_wordsBounded I limit hWords hClosed N bits
        (.ofWords a b hb hab upper lower) pos hpos
        (CachedWordCursor.ofWords_bounded I limit a b hb hab hw.2 upper lower hc.1 hc.2)
  | @coin w a b hb hab upper lower =>
    rw [hCursorEq] at hCursor
    unfold CachedWordsBounded
    refine ⟨hCursor.1, ?_⟩
    by_cases hz : a.isZero = true
    · rw [dite_eq_left hz]
      exact m.runCachedIndexed_wordsBounded I limit hWords hClosed N bits (.state lower) pos hpos hCursor.2.2
    rw [dite_eq_right hz]
    by_cases he : a.same b = true
    · rw [dite_eq_left he]
      exact m.runCachedIndexed_wordsBounded I limit hWords hClosed N bits (.state upper) pos hpos hCursor.2.1
    rw [dite_eq_right he]
    by_cases hRead : pos < N
    · rw [dite_eq_left hRead]
      dsimp only
      have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
      by_cases hd : bits ⟨pos, hRead⟩ = (a.coinStep b).1
      · rw [ite_eq_left hd]
        exact m.runCachedIndexed_wordsBounded I limit hWords hClosed N bits
          (.coin (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le upper lower) (pos + 1) (by omega) hCursor
      · rw [ite_eq_right hd]
        apply m.runCachedIndexed_wordsBounded I limit hWords hClosed N bits _ (pos + 1) (by omega)
        cases hBit : bits ⟨pos, hRead⟩
        · exact hCursor.2.1
        · exact hCursor.2.2
    · rw [dite_eq_right hRead]
      trivial
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp only [hCursorEq, cachedCursorRank]
  · have hp := m.progress s
    rw [hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

theorem runCached_wordsBounded {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (limit : ℕ) (hWords : ∀ s, I s → (m.step s).WordsHeight limit)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun _ => True))
    (R : ℕ) (s : S) (hI : I s) (bits : Fin R → Bool) :
    m.CachedWordsBounded I limit R bits (.state s) 0 (Nat.zero_le _) :=
  m.runCachedIndexed_wordsBounded I limit hWords hClosed R bits (.state s) 0 (Nat.zero_le _) hI

end Blotto.WordStateMachine
