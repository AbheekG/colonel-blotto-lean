import Blotto.GeneralPaperRoundedAdditionOperands

/-! The separate primitive-real implementation uses bounded real division.
Its complete price includes conversions, branching and metadata; no unit
cost is assigned to integer division in this implementation.
-/
namespace Blotto.GeneralPaperRoundedAdditionArithmetic
open GeneralPaperDyadicFloat GeneralPaperRoundedAdditionExecution
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem raw_work (unit p : ℕ) (high low : Number) (scale scaleWork : ℕ) :
    rawCost (fun _ => 1) unit p high low scale scaleWork=22 := by rfl

theorem ordered_annotation (power : ℕ → GeneralPaperPowerCeiling.Result × ℕ)
    (hPower : ∀ n, (power n).1=GeneralPaperScoreScaleParameters.powerRun n)
    (quotient : ℕ → ℕ → ℕ → ℕ × ℕ) (primitive : ℕ → ℕ) (W unit p : ℕ) (high low : Number) :
    (orderedWith power quotient primitive W unit p high low).1.work≤20*p+80 := by
  unfold orderedWith
  dsimp only
  split
  · dsimp only; omega
  · dsimp only
    rw [hPower,(GeneralPaperScoreScaleParameters.power_data _).2.2]
    omega

theorem ordered_work (unit p : ℕ) (high low : Number) :
    (orderedWith GeneralPaperAlignmentPowerPrice.arithmetic arithmeticQuotient (fun _ => 1) 1 unit p high low).2≤512*(p+1) := by
  unfold orderedWith
  dsimp only [GeneralPaperDyadicComparisonPrice.gapCost,GeneralPaperIntegerPrimitivePrice.binary,
    GeneralPaperIntegerWordPrice.compare]
  split
  · dsimp only; omega
  · rename_i hNear
    have hp := GeneralPaperAlignmentPowerPrice.arithmetic_work (GeneralPaperDyadicAlignment.gap high low)
    dsimp only
    rw [raw_work]
    unfold arithmeticQuotient
    dsimp only
    rw [GeneralPaperBoundedQuotient.run_work]
    omega

theorem work (unit p : ℕ) (left right : Number) :
    (arithmetic unit p left right).2≤2048*(p+1) := by
  unfold arithmetic addWith
  dsimp only [GeneralPaperIntegerWordPrice.compare,GeneralPaperNaturalPrimitivePrice.binary]
  split
  · dsimp only; omega
  · split
    · dsimp only; omega
    · split
      · dsimp only
        have h := ordered_work unit p left right
        omega
      · dsimp only
        have h := ordered_work unit p right left
        omega

end Blotto.GeneralPaperRoundedAdditionArithmetic
