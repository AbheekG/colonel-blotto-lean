import Blotto.SharedResourceRun
import Blotto.CachedWordCallbackWork

/-! Source event prices follow one-state control. The initial ready event is
priced once; a resolving coin prices its selected-update event and suppresses
the redundant ready event after materialization. No resource successors are
stored in the pending runtime representation. -/

namespace Blotto.WordStateMachine

def cachedCallbackTailWork {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match m.step state with
  | .done _ => 0
  | .ask a b hb hab upper lower => m.cachedCallbackWork charge N bits (.ofWords a b hb hab upper lower) pos hpos

theorem cachedCallbackWork_state {S α : Type*} (m : WordStateMachine S α) (charge : S → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (state : S) (pos : ℕ) (hpos : pos ≤ N) :
    m.cachedCallbackWork charge N bits (.state state) pos hpos = charge state + m.cachedCallbackTailWork charge N bits state pos hpos := by
  conv_lhs => unfold cachedCallbackWork
  unfold cachedCallbackTailWork
  cases m.step state <;> rfl

end Blotto.WordStateMachine
namespace Blotto.SharedResourceCursor

def callbackWork {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor L) (incoming : ℕ) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .ready state => incoming + match _hp : prepareResourceChoice state with
    | .done _ => 0
    | .ask p => callbackWork charge N bits (prepared p) 0 pos hpos
  | .coin choice a b hb hab =>
    if hz : a.isZero = true then callbackWork charge N bits (.ready (choice.select false))
        (charge (choice.successor false)) pos hpos else
      if he : a.same b = true then callbackWork charge N bits (.ready (choice.select true))
        (charge (choice.successor true)) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            callbackWork charge N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) 0 (pos + 1) (by omega)
          else callbackWork charge N bits (.ready (choice.select (!bits ⟨pos, hRead⟩)))
            (charge (choice.successor (!bits ⟨pos, hRead⟩))) (pos + 1) (by omega)
        else 0
termination_by (N - pos, cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    exact prepared_rank_lt state p _hp
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

def callbackWorkReference {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor L) (incoming : ℕ) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .ready state => incoming + (rationalResourceMachine L).cachedCallbackTailWork charge N bits (.ready state) pos hpos
  | .coin choice a b hb hab => (rationalResourceMachine L).cachedCallbackWork charge N bits
      (.coin a b hb hab (choice.successor true) (choice.successor false)) pos hpos

theorem callbackTailWork_materialize {n : ℕ} {L : Fin n → ℚ} (charge : RationalResourceCursor L → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : RationalResourceCursor L) (pos : ℕ) (hpos : pos ≤ N) :
    (rationalResourceMachine L).cachedCallbackTailWork charge N bits cursor pos hpos =
      (rationalResourceMachine L).cachedCallbackTailWork charge N bits (.ready cursor.materialize) pos hpos := rfl

end Blotto.SharedResourceCursor
