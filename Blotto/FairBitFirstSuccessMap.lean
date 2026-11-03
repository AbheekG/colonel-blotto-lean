import Blotto.FairBitFirstSuccess

/-! Postprocessing a returned value commutes with the actual bounded
short-circuit bit-block loop, while preserving every rejection outcome. -/

namespace Blotto.FairBitFirstSuccess

theorem run_map {α β : Type*} (N : ℕ) (trial : (Fin N → Bool) → Option α)
    (post : α → β) (attempts : ℕ) (bits : Fin (attempts * N) → Bool) :
    run N (fun seed => (trial seed).map post) attempts bits =
      (run N trial attempts bits).map post := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    rw [run, run]
    cases trial (firstBitBlock N (attempts * N) (flat bits)) with
    | none => exact ih _
    | some value => rfl

end Blotto.FairBitFirstSuccess
