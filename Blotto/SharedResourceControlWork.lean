import Blotto.SharedResourceRun
import Blotto.CachedControlWork

/-! The primary source prefix encodes each prepared word once and prices every
Boolean coin body, including its zero/one checks and the exhausting iteration.
No successor-state pair, runtime tracking flag or extra input packet is stored. -/

namespace Blotto.SharedResourceCursor

def controlWork {n : ℕ} {L : Fin n → ℚ} (encodingPrice coinPrice : ℕ → ℕ)
    (N : ℕ) (bits : Fin N → Bool) (cursor : SharedResourceCursor L) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  match cursor with
  | .ready state => match _hp : prepareResourceChoice state with
    | .done _ => 0
    | .ask p => encodingPrice (binaryWordWidth p.words.denominator) + controlWork encodingPrice coinPrice N bits (prepared p) pos hpos
  | @SharedResourceCursor.coin _ _ w choice a b hb hab =>
    coinPrice w + if hz : a.isZero = true then controlWork encodingPrice coinPrice N bits (.ready (choice.select false)) pos hpos else
      if he : a.same b = true then controlWork encodingPrice coinPrice N bits (.ready (choice.select true)) pos hpos else
        if hRead : pos < N then
          let next := a.coinStep b
          have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
          if bits ⟨pos, hRead⟩ = next.1 then
            controlWork encodingPrice coinPrice N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le) (pos + 1) (by omega)
          else controlWork encodingPrice coinPrice N bits (.ready (choice.select (!bits ⟨pos, hRead⟩))) (pos + 1) (by omega)
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


end Blotto.SharedResourceCursor
