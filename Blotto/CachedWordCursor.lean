import Blotto.WordStateMachineCore
import Blotto.FixedBinaryWord

/-! Pending coins retain equal-width Boolean numerator/denominator words.
The numerical cursor is only a refinement/proof view. Word encoding occurs
when a state requests a new coin, never during a pending digit iteration. -/

namespace Blotto

inductive CachedWordCursor (S : Type*) where
  | state (s : S)
  | coin {w : ℕ} (a b : FixedBinaryWord w) (positive : 0 < b.value)
      (normalized : a.value ≤ b.value) (upper lower : S)

namespace CachedWordCursor

def reference {S : Type*} : CachedWordCursor S → WordCursor S
  | .state s => .state s
  | .coin a b hb hab upper lower => .coin a.value b.value hb hab upper lower

def ofWords {S : Type*} (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (upper lower : S) : CachedWordCursor S :=
  let w := binaryWordWidth b
  let numerator := FixedBinaryWord.ofNat w a
  let denominator := FixedBinaryWord.ofNat w b
  have hB := FixedBinaryWord.value_ofNat w b (lt_pow_binaryWordWidth b)
  have hA := FixedBinaryWord.value_ofNat w a (hab.trans_lt (lt_pow_binaryWordWidth b))
  .coin numerator denominator (by rw [hB]; exact hb) (by rw [hA, hB]; exact hab) upper lower

theorem reference_ofWords {S : Type*} (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (upper lower : S) :
    (ofWords a b hb hab upper lower).reference = WordCursor.coin a b hb hab upper lower := by
  simp only [ofWords, reference, FixedBinaryWord.value_ofNat _ b (lt_pow_binaryWordWidth b),
    FixedBinaryWord.value_ofNat _ a (hab.trans_lt (lt_pow_binaryWordWidth b))]

end CachedWordCursor
namespace WordStateMachine

def cachedCursorRank {S α : Type*} (m : WordStateMachine S α) : CachedWordCursor S → ℕ
  | .state s => 2 * m.rank s + 1
  | .coin _ _ _ _ upper lower => 2 * (1 + max (m.rank upper) (m.rank lower))

theorem cachedCursorRank_reference {S α : Type*} (m : WordStateMachine S α) (cursor : CachedWordCursor S) :
    m.cachedCursorRank cursor = m.cursorRank cursor.reference := by cases cursor <;> rfl

def runCachedIndexed {S α : Type*} (m : WordStateMachine S α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor S) (pos : ℕ) (hpos : pos ≤ N) : Option α × ℕ :=
  match cursor with
  | .state s =>
    match _hs : m.step s with
    | .done value => (some value, pos)
    | .ask a b hb hab upper lower =>
      m.runCachedIndexed N bits (.ofWords a b hb hab upper lower) pos hpos
  | .coin a b hb hab upper lower =>
    if hz : a.isZero = true then m.runCachedIndexed N bits (.state lower) pos hpos else
      if he : a.same b = true then m.runCachedIndexed N bits (.state upper) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          let bit := bits ⟨pos, hRead⟩
          if bit = next.1 then
            m.runCachedIndexed N bits (.coin next.2 b hb (a.coinStep_normalized b hlt).le upper lower)
              (pos + 1) (by omega)
          else m.runCachedIndexed N bits (.state (if bit then lower else upper)) (pos + 1) (by omega)
        else (none, pos)
termination_by (N - pos, m.cachedCursorRank cursor)
decreasing_by
  all_goals simp_wf
  all_goals simp only [cachedCursorRank]
  · have hp := m.progress s
    rw [_hs] at hp
    simp only [CachedWordCursor.ofWords]
    omega
  all_goals omega

end WordStateMachine
end Blotto
