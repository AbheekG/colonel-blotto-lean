import Blotto.CachedEmissionWork
import Blotto.CachedCallbackPotentialUnder
import Blotto.WordMachineLaw
import Blotto.WordMachineSerialLaw

/-! Reachable leaf prices bound the one-time output charge at any indexed
position. This uses the original prices, with no runtime clipping or tests. -/

namespace Blotto.WordStateMachine

theorem cachedEmissionWork_bound_under {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (price : α → ℕ) (bound : ℕ)
    (hClosed : ∀ s, I s → (m.step s).Postcondition I (fun x => price x ≤ bound))
    (N : ℕ) (bits : Fin N → Bool) (state : S) (hI : I state) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedEmissionWork price N bits (.state state) pos hpos ≤ bound := by
  apply m.cachedCallbackWork_state_potential_under I _ (m.emissionCharge price) (fun _ => bound) _
    N bits state hI pos hpos
  · intro s hs
    have hc := hClosed s hs
    cases ht : m.step s with
    | done value => trivial
    | ask a b hb hab upper lower =>
      rw [ht] at hc
      exact hc
  · intro s hs
    have hc := hClosed s hs
    cases ht : m.step s with
    | done value =>
      rw [ht] at hc
      simpa only [emissionCharge, ht, WordTransition.Postcondition] using hc
    | ask a b hb hab upper lower => simp only [emissionCharge, ht, Nat.zero_add, le_refl, and_self]

theorem cachedEmissionWork_leaves_bound {S α : Type*} (m : WordStateMachine S α)
    (price : α → ℕ) (bound : ℕ) (N : ℕ) (bits : Fin N → Bool) (state : S)
    (hLeaves : (m.specification state).decode.ForLeaves (fun x => price x ≤ bound))
    (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedEmissionWork price N bits (.state state) pos hpos ≤ bound := by
  apply m.cachedEmissionWork_bound_under (fun s => (m.specification s).decode.ForLeaves (fun x => price x ≤ bound))
    price bound _ N bits state hLeaves pos hpos
  intro s hs
  cases ht : m.step s with
  | done value =>
    rw [m.specification_of_done s value ht] at hs
    exact hs
  | ask a b hb hab upper lower =>
    rw [m.specification_of_ask s a b hb hab upper lower ht] at hs
    exact hs

end Blotto.WordStateMachine
