import Blotto.RationalResourcePairBitPrice
import Blotto.WordMachineWordHeight

/-! Every reached resource request has numerator and denominator bounded by
the fixed input lattice. Restriction wrappers preserve those same words. -/

namespace Blotto.WordTransition

theorem restrict_wordsHeight {S α : Type*} (I : S → Prop) (P : α → Prop)
    (transition : WordTransition S α) (h : transition.Postcondition I P) (limit : ℕ)
    (hWords : transition.WordsHeight limit) : (transition.restrict I P h).WordsHeight limit := by
  cases transition <;> exact hWords

end Blotto.WordTransition
namespace Blotto

theorem rationalResourceStep_wordsHeight {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (D : ℕ) (hD : 0 < D) (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1)
    (hState : state.resource.OnLattice D) :
    (rationalResourceStep state).WordsHeight (binaryWordWidth D) := by
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
        let p := state.pair a b tail rfl
        have hPair : p.Lattice D := ⟨hL a, hL b, hState a, hState b⟩
        exact ⟨(p.words_num_le hD hPair (hUnit a)).trans_lt (lt_pow_binaryWordWidth D),
          (p.words_den_le hD hPair (hUnit a)).trans_lt (lt_pow_binaryWordWidth D)⟩

theorem rationalResourceMachine_wordsHeight {n : ℕ} (L : Fin n → ℚ) (D : ℕ) (hD : 0 < D)
    (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1) :
    ∀ cursor, rationalResourcePairInvariant L D cursor →
      ((rationalResourceMachine L).step cursor).WordsHeight (binaryWordWidth D) := by
  intro cursor hCursor
  exact rationalResourceStep_wordsHeight cursor.materialize D hD hL hUnit hCursor

end Blotto
