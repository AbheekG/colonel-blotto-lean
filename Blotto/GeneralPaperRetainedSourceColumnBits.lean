import Blotto.GeneralPaperRetainedCompilerPairBits
import Blotto.GeneralPaperRetainedSourceColumns

/-! Bit-priced geometric source, complete rational-row checks, physical
quantization and normalization on retained shared data. Native row and
column arrays coincide with the arithmetic execution. -/
namespace Blotto.GeneralPaperRetainedSourceColumnBits
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperInitializerPreparedPoint
open GeneralPaperProxyParameters
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {m T K : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=T) (hPos : 0<T) (hK : 0<K) (hDiv : K∣T) :
    (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)×Bool)×ℕ :=
  let rows := GeneralPaperRetainedSourceRows.run true model W k Qv a c hc weights Bc Br shared hs hT
  let columns := GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W hPos hK hDiv shared.Bc rows.1.1
  ((columns.1,rows.1.2),rows.2+columns.2+64*W)

theorem data {m K : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)
    (hPos : 0<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (hK : 0<K)
    (hDiv : K∣(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    GeneralPaperRowQuantizer.dictionary (run model W k Qv a c hc weights Bc Br shared hs hT hPos hK hDiv).1.1=
      GeneralPaperDictionary.normalize (GeneralPaperRowQuantizer.buildDivisible hPos hK hDiv
        (GeneralPaperCatalogueRationalTrajectory.rows a k Qv qbar weights Bc Br)) Bc := by
  dsimp only [run]
  rw [GeneralPaperNativeUnitSourceJoin.data,
    GeneralPaperRetainedSourceRows.data true model W k Qv a c hc weights Bc Br shared hs hT,
    GeneralPaperSourceRowsDriver.rational_data true model W k Qv qbar a c hc weights Bc Br shared hs]
  rw [hs]
  rfl

theorem actual_checked {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv) (shared : Shared m)
    (hs : shared=prepare (alphabet m k) k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (run model W k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1.2=true := by
  let rho := (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value
  have hDen : (ownBudget m k b reciprocal).den∣rho.den := by cases reciprocal <;> simp [ownBudget,rho]
  dsimp only [run]
  rw [GeneralPaperRetainedSourceRows.data true model W k Qv (alphabet m k) c hc weights _ _ shared hs hT]
  exact GeneralPaperSourceRowsDriver.checked true model W k Qv rho.den (prepare m k).qbar
    (alphabet m k) c hc weights _ _ shared hs hm hQv hw (own_positive m k b hb reciprocal).le rho.den_pos
    (GeneralPaperProxyClassifier.proxy_reduced_denominator m k b) hDen

theorem actual_models {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv) (shared : Shared m)
    (hs : shared=prepare (alphabet m k) k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (run model W k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1=
      (GeneralPaperRetainedSourceColumns.run model k Qv (alphabet m k) c hc weights _ _ shared hs hT
        (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
        (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1 := by
  apply Prod.ext
  · apply GeneralPaperRetainedBitData.dictionary_injective
    exact (data model W k Qv (prepare m k).qbar (alphabet m k) c hc weights _ _ shared hs hT _ _ _).trans
      (GeneralPaperRetainedSourceColumns.data model k Qv (prepare m k).qbar (alphabet m k) c hc weights _ _ shared hs hT _ _ _).symm
  · rw [actual_checked model W k Qv hm hQv b hb reciprocal c hc weights hw shared hs hT,
      GeneralPaperRetainedSourceColumns.actual_checked model k Qv hm hQv b hb reciprocal c hc weights hw shared hs hT]

theorem work {m K : ℕ} {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv) (Bc Br : ℚ)
    (shared : Shared m) (hs : shared=prepare a k Qv weights Bc Br)
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)
    (hPos : 0<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (hK : 0<K)
    (hDiv : K∣(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)
    (hB : RationalHeight Bc t) (hbc : rationalWordWidth Bc≤GeneralPaperTagHeight.word (a.lambda+1) 0)
    (hbr : rationalWordWidth Br≤GeneralPaperTagHeight.word (a.lambda+1) 0) (hW : 1≤W)
    (hIndex : binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows+K+m+1)≤W) :
    (run model W k Qv a c hc weights Bc Br shared hs hT hPos hK hDiv).2≤
      GeneralPaperSourceRowsDriver.bitProfile C d W m k Qv t a+
      GeneralPaperNativeUnitSourceJoin.profile model.rat W t (binaryWordWidth a.C)
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows m K
        (GeneralPaperNativeDivisibleColumns.blocks model.rat W (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows K hK).1.val+64*W := by
  let rows := GeneralPaperRetainedSourceRows.run true model W k Qv a c hc weights Bc Br shared hs hT
  have hRows := GeneralPaperSourceRowsDriver.bit_work hg W k Qv t a c hc weights Bc Br shared hs hw hB hbc hbr
  rw [←GeneralPaperRetainedSourceRows.data true model W k Qv a c hc weights Bc Br shared hs hT] at hRows
  have hHeight (i : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m) :
      RationalHeight ((rows.1.1.read i).read j) (binaryWordWidth a.C) := by
    dsimp only [rows]
    rw [GeneralPaperRetainedSourceRows.data true model W k Qv a c hc weights Bc Br shared hs hT,
      GeneralPaperSourceRowsDriver.rational_data true model W k Qv 0 a c hc weights Bc Br shared hs]
    simp only [GeneralPaperCatalogueRationalTrajectory.rows,FixedArrayTable.read_ofFn]
    exact GeneralPaperSourceScoreHeights.decoded_height m 0 a _
  have hColumns := GeneralPaperNativeUnitSourceJoin.work model.rat (fun w => w) model.monotone W t
    (binaryWordWidth a.C) hW hPos hK hDiv Bc hB rows.1.1 hHeight
    (fun i hi => (binaryWordWidth_mono (show i+1≤2*(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows+K+m+1 by omega)).trans hIndex)
  have hBudget : shared.Bc=Bc := by rw [hs]; rfl
  change rows.2+(GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W hPos hK hDiv shared.Bc rows.1.1).2+64*W≤_
  rw [hBudget]
  exact Nat.add_le_add_right (Nat.add_le_add hRows hColumns) _

end Blotto.GeneralPaperRetainedSourceColumnBits
