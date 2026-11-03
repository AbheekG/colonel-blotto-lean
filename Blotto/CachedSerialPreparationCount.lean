import Blotto.CachedSerialHandoffWork
import Blotto.CachedSerialSourceEquality

/-! A rank-zero source reaches handoff without reading a bit. Preparation is
counted once even if the terminal continuation immediately exhausts its cap. -/

namespace Blotto.WordStateMachine

theorem cachedSerialPreparationCount_zero_rank {S α β : Type*} {T : α → Type*}
    (m : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) (state : S) (hRank : m.rank state = 0)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (m.serial next start C hC).cachedCallbackWork (serialPreparationCharge m (fun _ => 1))
      N bits (.state (.source state)) pos hpos = 1 := by
  cases hs : m.step state with
  | done value =>
    have h := m.cachedSerialDoneHandoffWork next start C hC (fun _ => 1) (fun _ _ => 0)
      state value hs N bits pos hpos
    rw [serialHandoffCharge_zeroTerminal, (next value).cachedCallbackWork_zero, Nat.add_zero] at h
    exact h
  | ask a b hb hab upper lower =>
    have hp := m.progress state
    rw [hs] at hp
    omega

end Blotto.WordStateMachine
