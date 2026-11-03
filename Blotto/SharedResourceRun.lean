import Blotto.SharedResourceCursor

/-! Tail-recursive indexed resource sampling with one pending resource state.
Both endpoint values are retained, while only the chosen branch is materialized.
The decoder is used for termination/refinement proofs, never by this runtime. -/

namespace Blotto.SharedResourceCursor

theorem prepare_step {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (p : PreparedResourceChoice L) (h : prepareResourceChoice state = .ask p) :
    (rationalResourceMachine L).step (.ready state) =
      .ask p.words.numerator p.words.denominator p.words.denominator_pos p.words.normalized
        (p.choice.successor true) (p.choice.successor false) := by
  have he := prepareResourceChoice_refines state
  rw [h] at he
  exact he.symm

theorem prepared_rank_lt {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (p : PreparedResourceChoice L) (h : prepareResourceChoice state = .ask p) :
    (prepared p).rank < (SharedResourceCursor.ready state).rank := by
  have hp := (rationalResourceMachine L).progress (.ready state)
  rw [prepare_step state p h] at hp
  rw [rank, rank, decode_prepared]
  simp only [CachedWordCursor.ofWords, WordStateMachine.cachedCursorRank, decode]
  omega

theorem selected_rank_lt {n : ℕ} {L : Fin n → ℚ} {w : ℕ} (choice : ResourceChoice L)
    (a b : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value) (branch : Bool) :
    (SharedResourceCursor.ready (choice.select branch)).rank < (SharedResourceCursor.coin choice a b hb hab).rank := by
  cases branch <;>
    change 2 * ((choice.select _).active.length - 1) + 1 <
      2 * (1 + max ((choice.select true).active.length - 1) ((choice.select false).active.length - 1))
  all_goals omega

def runIndexed {n : ℕ} {L : Fin n → ℚ} (N : ℕ) (bits : Fin N → Bool)
    (cursor : SharedResourceCursor L) (pos : ℕ) (hpos : pos ≤ N) : Option (RationalActiveResources L) × ℕ :=
  match cursor with
  | .ready state => match _hp : prepareResourceChoice state with
    | .done value => (some value, pos)
    | .ask p => runIndexed N bits (prepared p) pos hpos
  | .coin choice a b hb hab =>
    if hz : a.isZero = true then runIndexed N bits (.ready (choice.select false)) pos hpos else
      if he : a.same b = true then runIndexed N bits (.ready (choice.select true)) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            runIndexed N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos + 1) (by omega)
          else runIndexed N bits (.ready (choice.select (!bits ⟨pos, hRead⟩))) (pos + 1) (by omega)
        else (none, pos)
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

def run {n : ℕ} {L : Fin n → ℚ} (N : ℕ) (state : RationalActiveResources L) (bits : Fin N → Bool) :
    Option (RationalActiveResources L) × ℕ := runIndexed N bits (.ready state) 0 (Nat.zero_le N)

end Blotto.SharedResourceCursor
