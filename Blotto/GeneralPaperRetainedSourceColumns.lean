import Blotto.GeneralPaperRetainedSourceRows

/-! Source, checked whole rational rows, physical quantization and unit
normalization execute once from retained shared data. Runtime T/K controls
are supplied from their cached fields; all equality/size premises erase. -/
namespace Blotto.GeneralPaperRetainedSourceColumns
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperInitializerPreparedPoint
open GeneralPaperProxyParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {m T K : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=T) (hPos : 0<T) (hK : 0<K) (hDiv : K∣T) :
    (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×Bool)×ℕ :=
  let rows := GeneralPaperRetainedSourceRows.run false model 1 k Qv a c hc weights Bc Br shared hs hT
  let columns := GeneralPaperNativeUnitSourceJoin.run (fun _ => 1) (fun _ => 1) 1 hPos hK hDiv shared.Bc rows.1.1
  ((columns.1,rows.1.2),rows.2+columns.2+64)

theorem data {m K : ℕ} (model : RationalCostModel) (k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)
    (hPos : 0<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (hK : 0<K)
    (hDiv : K∣(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    GeneralPaperRowQuantizer.dictionary (run model k Qv a c hc weights Bc Br shared hs hT hPos hK hDiv).1.1=
      GeneralPaperDictionary.normalize (GeneralPaperRowQuantizer.buildDivisible hPos hK hDiv
        (GeneralPaperCatalogueRationalTrajectory.rows a k Qv qbar weights Bc Br)) Bc := by
  dsimp only [run]
  rw [GeneralPaperNativeUnitSourceJoin.data,
    GeneralPaperRetainedSourceRows.data false model 1 k Qv a c hc weights Bc Br shared hs hT,
    GeneralPaperSourceRowsDriver.rational_data false model 1 k Qv qbar a c hc weights Bc Br shared hs]
  rw [hs]
  rfl

theorem actual_data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℝ) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (weights : FixedArrayTable m ℕ) (shared : Shared m)
    (hs : shared=prepare (alphabet m k) k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    GeneralPaperRowQuantizer.dictionary (run model k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1.1=
      GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal := by
  exact data model k Qv (GeneralPaperProxyParameters.prepare m k).qbar (alphabet m k) c hc weights _ _ shared hs hT _ _ _

theorem actual_checked {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv) (shared : Shared m)
    (hs : shared=prepare (alphabet m k) k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (run model k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1.2=true := by
  let rho := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
  have hDen : (ownBudget m k b reciprocal).den∣rho.den := by
    cases reciprocal <;> simp [ownBudget,rho]
  dsimp only [run]
  rw [GeneralPaperRetainedSourceRows.data false model 1 k Qv (alphabet m k) c hc weights _ _ shared hs hT]
  exact GeneralPaperSourceRowsDriver.checked false model 1 k Qv rho.den (GeneralPaperProxyParameters.prepare m k).qbar
    (alphabet m k) c hc weights _ _ shared hs hm hQv hw (own_positive m k b hb reciprocal).le rho.den_pos
    (GeneralPaperProxyClassifier.proxy_reduced_denominator m k b) hDen

end Blotto.GeneralPaperRetainedSourceColumns
