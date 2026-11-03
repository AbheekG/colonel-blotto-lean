import Blotto.CachedTrackedEncodingWork
import Blotto.WordMachineSerialClosedWork

/-! A serial source tag charges resource coins only. Source request words
inherit their own bound; the continuation's true words need no source bound. -/

namespace Blotto.WordStateMachine

def serialSourceTag {S α : Type*} {T : α → Type*} : SerialState S α T → Bool
  | .source _ => true
  | .continuation _ _ => false

theorem serial_sourceTrackedWordsHeight {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (I : S → Prop) (limit : ℕ)
    (hWords : ∀ s, I s → (m.step s).WordsHeight limit) :
    ∀ cursor, serialInvariant I cursor →
      ((m.serial next start C hC).step cursor).TrackedWordsHeight serialSourceTag limit := by
  intro cursor hI
  cases cursor with
  | source s =>
    have hw := hWords s hI
    cases hs : m.step s with
    | done a =>
      cases ht : (next a).step (start a) <;>
        simp [serial, serialTransition, WordTransition.mapState, WordTransition.TrackedWordsHeight,
          trackedCoin, serialSourceTag, hs, ht]
    | ask a b hb hab upper lower =>
      rw [hs] at hw
      simpa [serial, serialTransition, WordTransition.TrackedWordsHeight, WordTransition.WordsHeight, trackedCoin, serialSourceTag, hs] using hw
  | continuation a s =>
    cases ht : (next a).step s <;>
      simp [serial, serialTransition, WordTransition.mapState, WordTransition.TrackedWordsHeight,
        trackedCoin, serialSourceTag, ht]

end Blotto.WordStateMachine
