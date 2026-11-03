import Blotto.BinaryTerminalRoutes

/-! Group-size proof transports preserve the actual proportional output rule.
They are semantic joins only; runtime cached routes keep their native size. -/

namespace Blotto.BinaryTerminalRoutes

theorem transport_emit {n m k : ℕ} (he : m=k) (source : RationalProportionalGroups n m) (row : Fin k → ℚ) (j : Fin n) :
    ((transportPartition he source).emit (transportPartition he source).routes row).allocation j =
      (source.emit source.routes (fun g => row (g.cast he))).allocation j := by cases he; rfl

theorem transport_emitMixed {n m k : ℕ} (he : m=k) (source : RationalProportionalGroups n m) (pivot : Fin n)
    (row : Fin (k+1) → ℚ) (j : Fin n) :
    ((transportPartition he source).emitMixed (transportPartition he source).routes pivot row).allocation j =
      (source.emitMixed source.routes pivot (fun g => row (g.cast (congrArg (fun size => size+1) he)))).allocation j := by
  cases he
  rfl

end Blotto.BinaryTerminalRoutes
