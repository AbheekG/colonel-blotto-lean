import Blotto.CachedSerialFactoryWork
import Blotto.CachedSerialPreparationUnder

/-! Reached source/continuation prices bound individual factory and one-time
preparation callback charges. No condition is imposed on unreachable outputs. -/

namespace Blotto.WordStateMachine

theorem serialFactoryCharge_bound_under {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (I : S → Prop) (P : α → Prop) (J : ∀ a, T a → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (price : α → ℕ) (bound : ℕ)
    (hPrice : ∀ a, P a → price a ≤ bound) (cursor : SerialState S α T)
    (hCursor : serialHandoffInvariant I P J cursor) : serialFactoryCharge m start price cursor ≤ 2 * bound := by
  cases cursor with
  | source state =>
    have hp := hSource state hCursor
    cases hs : m.step state with
    | done value =>
      rw [hs] at hp
      have hc := hPrice value hp
      simp only [serialFactoryCharge, serialHandoffCharge, hs]
      omega
    | ask a b hb hab upper lower => simp only [serialFactoryCharge, serialHandoffCharge, hs, Nat.zero_le]
  | continuation value state =>
    have hc := hPrice value hCursor.1
    change price value ≤ 2 * bound
    omega

theorem serialPreparationCharge_bound_under {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (I : S → Prop) (P : α → Prop) (J : ∀ a, T a → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (price : α → ℕ) (bound : ℕ)
    (hPrice : ∀ a, P a → price a ≤ bound) (cursor : SerialState S α T)
    (hCursor : serialHandoffInvariant I P J cursor) : serialPreparationCharge m price cursor ≤ bound := by
  cases cursor with
  | source state =>
    have hp := hSource state hCursor
    cases hs : m.step state with
    | done value =>
      rw [hs] at hp
      simpa only [serialPreparationCharge, hs] using hPrice value hp
    | ask a b hb hab upper lower => simp only [serialPreparationCharge, hs, Nat.zero_le]
  | continuation value state => exact Nat.zero_le _

theorem serialHandoffCharge_bound_under {S α : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (start : ∀ a, T a) (I : S → Prop) (P : α → Prop) (J : ∀ a, T a → Prop)
    (hSource : ∀ s, I s → (m.step s).Postcondition I P) (hStart : ∀ a, P a → J a (start a))
    (price : α → ℕ) (charge : ∀ a, T a → ℕ) (A B : ℕ)
    (hPrice : ∀ a, P a → price a ≤ A) (hCharge : ∀ a, P a → ∀ state, J a state → charge a state ≤ B)
    (cursor : SerialState S α T) (hCursor : serialHandoffInvariant I P J cursor) :
    serialHandoffCharge m start price charge cursor ≤ A + B := by
  cases cursor with
  | source state =>
    have hp := hSource state hCursor
    cases hs : m.step state with
    | done value =>
      rw [hs] at hp
      have hP := hPrice value hp
      have hC := hCharge value hp (start value) (hStart value hp)
      simp only [serialHandoffCharge, hs]
      omega
    | ask a b hb hab upper lower => simp only [serialHandoffCharge, hs, Nat.zero_le]
  | continuation value state =>
    have hC := hCharge value hCursor.1 state hCursor.2
    change charge value state ≤ A + B
    omega

end Blotto.WordStateMachine
