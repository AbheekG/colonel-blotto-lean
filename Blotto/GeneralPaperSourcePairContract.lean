import Blotto.GeneralPaperUnchangedBudgetDirections

/-! The actual pair's whole-row hard budgets and original label tables,
with transfer security relative to the literal two source laws. Only ONE
modified defender contributes m/S; both quantizers contribute 2/K.
-/
namespace Blotto.GeneralPaperSourcePairContract
open GeneralPaperProxyParameters GeneralPaperDictionary GeneralPaperSourceInitializer GeneralPaperInitializerPreparedPoint
open GeneralPaperSourcePairRun
open scoped BigOperators Classical
set_option autoImplicit false

structure Contract {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ)
    (pair : Pair (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K) : Prop where
  rich_unit : GeneralPaperTransferPreparation.UnitDictionary pair.rich
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
  poor_unit : GeneralPaperTransferPreparation.UnitDictionary pair.poor
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
  rich_labels : pair.rich.label=(prepared k Qv hQv weights hp hs b false).dictionary.label
  poor_labels : pair.poor.label=(prepared k Qv hQv weights hp hs b true).dictionary.label
  security_bound :
    security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
        (law pair.rich (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (1/b)
        (law pair.poor (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b false:ℝ)
        (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b false))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (opposingBudget m k b true:ℝ)
        (law (GeneralPaperRowQuantizer.original (sourceRows k Qv weights b true))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S

end Blotto.GeneralPaperSourcePairContract
