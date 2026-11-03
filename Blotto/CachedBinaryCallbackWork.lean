import Blotto.WordMachineChoice
import Blotto.CachedCallbackBounds

/-! Root and branch callback prices share the native binary controller's
single cap and current position. Closed branch invariants propagate only down
the selected branch, without runtime tests or an intermediate sampler. -/

namespace Blotto

def binaryInvariant {S T : Type*} (I : S → Prop) (J : T → Prop) : BinaryState S T → Prop
  | .start => True
  | .upper s => I s
  | .lower t => J t

def binaryCallbackCharge {S T : Type*} (root : ℕ) (upper : S → ℕ) (lower : T → ℕ) : BinaryState S T → ℕ
  | .start => root
  | .upper s => upper s
  | .lower t => lower t

theorem binaryInvariant_closed {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) (I : S → Prop) (J : T → Prop) (hA : I sa) (hB : J sb)
    (hAC : ∀ s, I s → (a.step s).Postcondition I (fun _ => True))
    (hBC : ∀ t, J t → (b.step t).Postcondition J (fun _ => True)) :
    ∀ cursor, binaryInvariant I J cursor →
      ((binaryMachine w a b sa sb).step cursor).Postcondition (binaryInvariant I J) (fun _ => True) := by
  intro cursor hCursor
  cases cursor with
  | start => exact ⟨hA, hB⟩
  | upper s =>
    have hp := hAC s hCursor
    cases hs : a.step s with
    | done value => simp [binaryMachine, binaryTransition, hs, WordTransition.mapState, WordTransition.Postcondition]
    | ask n d hd hnd upper lower =>
      rw [hs] at hp
      simpa only [binaryMachine, binaryTransition, hs, WordTransition.mapState, WordTransition.Postcondition, binaryInvariant] using hp
  | lower t =>
    have hp := hBC t hCursor
    cases hs : b.step t with
    | done value => simp [binaryMachine, binaryTransition, hs, WordTransition.mapState, WordTransition.Postcondition]
    | ask n d hd hnd upper lower =>
      rw [hs] at hp
      simpa only [binaryMachine, binaryTransition, hs, WordTransition.mapState, WordTransition.Postcondition, binaryInvariant] using hp

theorem binaryCallbackCharge_bound_under {S T : Type*} (I : S → Prop) (J : T → Prop)
    (root bound : ℕ) (upper : S → ℕ) (lower : T → ℕ) (hRoot : root ≤ bound)
    (hUpper : ∀ s, I s → upper s ≤ bound) (hLower : ∀ t, J t → lower t ≤ bound) :
    ∀ cursor, binaryInvariant I J cursor → binaryCallbackCharge root upper lower cursor ≤ bound := by
  intro cursor hCursor
  cases cursor with
  | start => exact hRoot
  | upper s => exact hUpper s hCursor
  | lower t => exact hLower t hCursor

theorem cachedBinaryCallbackWork_bound_under {S T α : Type*} (w : ProbabilityWords) (a : WordStateMachine S α) (b : WordStateMachine T α)
    (sa : S) (sb : T) (I : S → Prop) (J : T → Prop) (hA : I sa) (hB : J sb)
    (hAC : ∀ s, I s → (a.step s).Postcondition I (fun _ => True))
    (hBC : ∀ t, J t → (b.step t).Postcondition J (fun _ => True))
    (root bound : ℕ) (upper : S → ℕ) (lower : T → ℕ) (hRoot : root ≤ bound)
    (hUpper : ∀ s, I s → upper s ≤ bound) (hLower : ∀ t, J t → lower t ≤ bound)
    (C : ℕ) (hRank : (binaryMachine w a b sa sb).rank .start ≤ C)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (binaryMachine w a b sa sb).cachedCallbackWork (binaryCallbackCharge root upper lower)
      N bits (.state .start) pos hpos ≤ bound * (C + 1) := by
  have hp := (binaryMachine w a b sa sb).cachedCallbackWork_state_bound_under
    (binaryInvariant I J) (binaryInvariant_closed w a b sa sb I J hA hB hAC hBC)
    (binaryCallbackCharge root upper lower) bound
    (binaryCallbackCharge_bound_under I J root bound upper lower hRoot hUpper hLower)
    N bits .start trivial pos hpos
  exact hp.trans (Nat.mul_le_mul_left bound (Nat.add_le_add_right hRank 1))

end Blotto
