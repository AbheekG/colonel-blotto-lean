import Blotto.RationalResourceHeightInvariant
import Blotto.RationalResourceWordHeight

/-! Local request words follow the actual shared pair program and reached
field heights. The fixed-round estimate is not used for the general source. -/

namespace Blotto.WordTransition

theorem mapState_wordsHeight {S T α : Type*} (f : S → T) (t : WordTransition S α) (limit : ℕ)
    (h : t.WordsHeight limit) : (t.mapState f).WordsHeight limit := by cases t <;> exact h

theorem mapValue_wordsHeight {S α β : Type*} (f : α → β) (t : WordTransition S α) (limit : ℕ)
    (h : t.WordsHeight limit) : (t.mapValue f).WordsHeight limit := by cases t <;> exact h

end Blotto.WordTransition
namespace Blotto

theorem rationalResourceStep_fieldsWordsHeight {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (t : ℕ) (ht : 2 ≤ t) (hCaps : ∀ j, RationalHeight (L j) t) (hResource : state.resource.HeightAt t) :
    (rationalResourceStep state).WordsHeight (expressionHeightBudget t 4) := by
  rw [rationalResourceStep_refines]
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => trivial
    | cons a rest =>
      cases rest with
      | nil => trivial
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        have hp : (state.pair a b tail rfl).FieldsHeight t := ⟨hCaps a, hCaps b, hResource a, hResource b⟩
        exact hp.words ht

theorem rationalResourceHeightInvariant_wordsHeight {n : ℕ} (L : Fin n → ℚ) (C s : ℕ) (hs : 2 ≤ s)
    (hCaps : ∀ j, RationalHeight (L j) s) (cursor : RationalResourceCursor L)
    (hCursor : rationalResourceHeightInvariant L C s cursor) :
    ((rationalResourceMachine L).step cursor).WordsHeight (expressionHeightBudget s (3 * C + 4)) := by
  have hp := rationalResourceStep_fieldsWordsHeight cursor.materialize _ (hs.trans (expressionHeightBudget_ge_input s (3 * C)))
    (fun j => (hCaps j).mono (expressionHeightBudget_ge_input s (3 * C)))
    (rationalResourceHeightInvariant_resource L C s cursor hCursor)
  change (rationalResourceStep cursor.materialize).WordsHeight (expressionHeightBudget s (3 * C + 4))
  simpa only [expressionHeightBudget_comp] using hp

end Blotto
