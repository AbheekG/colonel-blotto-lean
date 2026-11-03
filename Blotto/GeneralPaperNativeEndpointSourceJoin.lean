import Blotto.GeneralPaperNativeEndpointColumnLaw

/-! The actual source's retained physical labels feed endpoint anchors.
The exact modified-defender unit/security contract transfers to those same
columns. Endpoint compilation is observed here; the once-only priced full
compiler/preparation driver remains a separate composition obligation. -/
namespace Blotto.GeneralPaperNativeEndpointSourceJoin
open GeneralPaperSourceWordGrowth GeneralPaperInitializerPreparedPoint GeneralPaperSourceEndpointBranch
set_option autoImplicit false
set_option maxHeartbeats 2800000

theorem source_labels {bits : Bool} (model : RationalCostModel) (W : ℕ) (x : Input) (price index : ℕ → ℕ) (A : ℕ)
    (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j) :
    let columns := (GeneralPaperNativeUnitSourceJoin.run price index A
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)
      (GeneralPaperScoreScaleParameters.labels_positive x.m x.k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows x.m (alphabet x).lambda x.k)
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)
      (GeneralPaperSourceRowsSharpContract.preparedRun bits model W x).1.1).1
    (GeneralPaperRowQuantizer.dictionary columns).label=
      (GeneralPaperSourceInitializer.prepared x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) x.reciprocal).dictionary.label := by
  dsimp only
  exact congrArg (fun d => d.label)
    ((GeneralPaperNativeUnitSourceJoin.source_data (bits:=bits) model W x price index A).trans
      (GeneralPaperSourceUnchangedDictionary.eq_prepared x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) x.reciprocal))

theorem source_data {bits : Bool} (model : RationalCostModel) (W : ℕ) (x : Input) (price index : ℕ → ℕ) (A : ℕ)
    (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j)
    (result : Result (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (GeneralPaperProxyParameters.prepare x.m x.k).K)
    (hLabels : result.labels=
      (GeneralPaperSourceInitializer.prepared x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) x.reciprocal).dictionary.label) :
    let columns := (GeneralPaperNativeUnitSourceJoin.run price index A
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)
      (GeneralPaperScoreScaleParameters.labels_positive x.m x.k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows x.m (alphabet x).lambda x.k)
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)
      (GeneralPaperSourceRowsSharpContract.preparedRun bits model W x).1.1).1
    GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price index A result.choice columns).1=
      GeneralPaperEndpointDictionary.dictionary result :=
  GeneralPaperNativeEndpointColumnLaw.result_data price index A result _
    ((source_labels model W x price index A hQv hp).trans hLabels.symm)

theorem source_contract {bits : Bool} (model : RationalCostModel) (W : ℕ) (x : Input) (price index : ℕ → ℕ) (A : ℕ)
    (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j) (budget : ℝ) (hBudget : 0≤budget)
    (result : Result (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (GeneralPaperProxyParameters.prepare x.m x.k).K)
    (hc : Contract (GeneralPaperSourceInitializer.prepared x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) x.reciprocal).dictionary
      (GeneralPaperNativeRationalValues.selector x.Qv hQv x.weights hp x.weight_sum) (GeneralPaperProxyParameters.prepare x.m x.k).S
      (GeneralPaperSourceInitializer.prepared x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) x.reciprocal).threshold budget result) :
    let columns := (GeneralPaperNativeUnitSourceJoin.run price index A
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)
      (GeneralPaperScoreScaleParameters.labels_positive x.m x.k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows x.m (alphabet x).lambda x.k)
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal)
      (GeneralPaperSourceRowsSharpContract.preparedRun bits model W x).1.1).1
    let d := GeneralPaperRowQuantizer.dictionary (GeneralPaperNativeEndpointColumns.run price index A result.choice columns).1
    GeneralPaperTransferPreparation.UnitDictionary d
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k) (GeneralPaperScoreScaleParameters.labels_positive x.m x.k) ∧
      security (GeneralPaperNativeRationalValues.selector x.Qv hQv x.weights hp x.weight_sum).values budget
        (GeneralPaperDictionary.law d (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)).law≤
      security (GeneralPaperNativeRationalValues.selector x.Qv hQv x.weights hp x.weight_sum).values
        (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal:ℝ)
        (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.original
          (GeneralPaperSourceInitializer.sourceRows x.k x.Qv x.weights (x.b:ℝ) x.reciprocal))
          (GeneralPaperTrajectoryParameters.rows_positive (alphabet x).lambda x.k)).law+
        1/((GeneralPaperProxyParameters.prepare x.m x.k).K:ℝ)+(x.m:ℝ)/(GeneralPaperProxyParameters.prepare x.m x.k).S := by
  dsimp only
  rw [source_data model W x price index A hQv hp result hc.1]
  exact GeneralPaperSourceModifiedDictionary.of_contract x.k x.Qv hm hQv x.weights hp x.weight_sum (x.b:ℝ)
    (by exact_mod_cast x.hb) x.reciprocal budget hBudget result hc

end Blotto.GeneralPaperNativeEndpointSourceJoin
