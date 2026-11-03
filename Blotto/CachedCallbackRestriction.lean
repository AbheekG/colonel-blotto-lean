import Blotto.CachedCallbackReindex

/-! Erasing invariant and output proof wrappers preserves arbitrary callback
prices. This is a work theorem, independent of output-law refinement. -/

namespace Blotto.WordTransition

theorem restrict_erase {S α : Type*} (I : S → Prop) (P : α → Prop)
    (t : WordTransition S α) (h : t.Postcondition I P) :
    ((t.restrict I P h).mapValue Subtype.val).mapState Subtype.val = t := by
  cases t <;> rfl

end Blotto.WordTransition
namespace Blotto.WordStateMachine

theorem cachedCallbackWork_restricted {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (P : α → Prop) (hI : ∀ s, I s → (m.step s).Postcondition I P)
    (charge : S → ℕ) (N : ℕ) (bits : Fin N → Bool)
    (cursor : CachedWordCursor {s // I s}) (pos : ℕ) (hpos : pos ≤ N) :
    (m.restricted I P hI).cachedCallbackWork (fun s => charge s.1) N bits cursor pos hpos =
      m.cachedCallbackWork charge N bits (cursor.mapState Subtype.val) pos hpos := by
  symm
  apply (m.restricted I P hI).cachedCallbackWork_reindex_values m Subtype.val Subtype.val
    _ (fun s => charge s.1) charge (fun _ => rfl)
  intro s
  exact (WordTransition.restrict_erase I P (m.step s.1) (hI s.1 s.2)).symm

theorem runCachedCallbackWork_restricted {S α : Type*} (m : WordStateMachine S α)
    (I : S → Prop) (P : α → Prop) (hI : ∀ s, I s → (m.step s).Postcondition I P)
    (charge : S → ℕ) (R : ℕ) (s : {s // I s}) (bits : Fin R → Bool) :
    (m.restricted I P hI).runCachedCallbackWork (fun q => charge q.1) R s bits =
      m.runCachedCallbackWork charge R s.1 bits :=
  m.cachedCallbackWork_restricted I P hI charge R bits (.state s) 0 (Nat.zero_le R)

end Blotto.WordStateMachine
