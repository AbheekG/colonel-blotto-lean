import Blotto.GeneralPaperSourceModifiedDictionary

/-! Unchanged defenders only quantize and normalize the source rows.
No unused strict-score DP is executed on this path. Its security follows
from the actual source at the weakly smaller opposing budget.
-/
namespace Blotto.GeneralPaperSourceUnchangedDictionary
open GeneralPaperProxyParameters GeneralPaperSourceInitializer GeneralPaperInitializerPreparedPoint
open GeneralPaperDictionary GeneralPaperTransferPreparation
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def run {m : ℕ} (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℝ) (reciprocal : Bool) :=
  let rows := sourceRows k Qv weights b reciprocal
  let quantized := GeneralPaperRowQuantizer.buildDivisible (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) rows
  normalize quantized (ownBudget m k b reciprocal)

theorem eq_prepared {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    run k Qv weights b reciprocal=(prepared k Qv hQv weights hp hs b reciprocal).dictionary := rfl

theorem unit {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    UnitDictionary (run k Qv weights b reciprocal) (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k) :=
  GeneralPaperSourcePoorZero.prepared_unit k Qv hm hQv weights hp hs b hb reciprocal

theorem bound {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (budget : ℝ) (hBudget : 0≤budget)
    (hSmaller : budget≤((opposingBudget m k b reciprocal/ownBudget m k b reciprocal:ℚ):ℝ)) :
    security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values budget
      (law (run k Qv weights b reciprocal) (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b reciprocal:ℝ)
        (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b reciprocal))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+1/((prepare m k).K:ℝ) :=
  unchanged_bound (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (sourceRows k Qv weights b reciprocal) (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (own_positive m k b hb reciprocal) (GeneralPaperSourceModifiedDictionary.opposing_positive m k b hb reciprocal).le
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
    (source_rows_feasible k Qv hm hQv weights hs b hb reciprocal) budget hBudget hSmaller

end Blotto.GeneralPaperSourceUnchangedDictionary
