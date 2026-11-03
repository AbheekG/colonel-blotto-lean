import Blotto.GeneralPaperSourceColumnCallerStorageRates

/-! Literal retained source-column parent and actual unchanged source
output, summed with all source-row/unit-source/strict/endpoint children. -/
namespace Blotto.GeneralPaperSourceColumnCallerStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def sourceRows {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :=
  GeneralPaperRetainedSourceRows.run true model W k Qv (alphabet m k)
    (GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv) rfl weights
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)) rfl rfl
noncomputable def unitColumns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :=
  GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) (ownBudget m k b reciprocal)
    (sourceRows model W k Qv weights b reciprocal).1.1
noncomputable def run {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :=
  GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k)
    (GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv) rfl weights
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)) rfl rfl
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) : ℕ := GeneralPaperRetainedSourceColumnCallerStorage.window W k Qv
  (sourceRows model W k Qv weights b reciprocal) (unitColumns model W k Qv weights b reciprocal) (run model W k Qv weights b reciprocal)

theorem rows_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) : (sourceRows model W k Qv weights b reciprocal).1.1=
      GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal :=
  GeneralPaperSourceRowsCallerStorage.retained_rows_data model W k Qv weights b reciprocal _ rfl _ rfl rfl

theorem unit_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) : unitColumns model W k Qv weights b reciprocal=
      GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
        (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) (ownBudget m k b reciprocal)
        (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) := by
  unfold unitColumns
  rw [rows_data]

theorem native_columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) : (run model W k Qv weights b reciprocal).1.1=
      GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal :=
  GeneralPaperSourceUnitCallerStorage.retained_columns model W k Qv weights b reciprocal _ rfl _ rfl rfl

theorem retained_form {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (shared : GeneralPaperCatalogueShared.Shared m)
    (hs : shared=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    window model W k Qv weights b reciprocal=
      let rows := GeneralPaperRetainedSourceRows.run true model W k Qv (alphabet m k) c hc weights _ _ shared hs hT
      let columns := GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
        (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) shared.Bc rows.1.1
      let result := GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights _ _ shared hs hT
        (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
      GeneralPaperRetainedSourceColumnCallerStorage.window W k Qv rows columns result := by
  subst c
  subst shared
  rfl

theorem source_column {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W) :
    window model W k Qv weights b reciprocal≤GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv ∧
      (run model W k Qv weights b reciprocal).2≤GeneralPaperRetainedSourceColumnCallerStorage.price W
        (GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv)
        (GeneralPaperSourceColumnCallerStorageRates.unitPrice model W m k) := by
  let rows := sourceRows model W k Qv weights b reciprocal
  let columns := unitColumns model W k Qv weights b reciprocal
  let result := run model W k Qv weights b reciprocal
  let R := GeneralPaperSourceUnitCallerStorageRates.operandWidth m k
  have hP := GeneralPaperSourceRowsCallerStorage.retained_work hg W k Qv weights hs b hb reciprocal _ rfl _ rfl rfl
  change rows.2≤GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv at hP
  have hQ : columns.2≤GeneralPaperSourceColumnCallerStorageRates.unitPrice model W m k := by
    dsimp only [columns]
    rw [unit_data]
    exact (GeneralPaperSourceUnitCallerStorage.source_unit model W k Qv weights b hb reciprocal hW hK hM hScatter).2
  have hRows : ∀ i j,rationalWordWidth ((rows.1.1.read i).read j)≤R := by
    intro i j
    dsimp only [rows]
    rw [rows_data]
    have h := rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal i j)
    exact h.trans (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight;omega)
  have hColumns : GeneralPaperEnclosingSourceOwners.columnsFoot W columns.1≤
      GeneralPaperEnclosingSourceOwners.columnsProfile W (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K R := by
    dsimp only [columns]
    rw [unit_data]
    apply GeneralPaperEnclosingSourceOwners.columns_bound W R
    intro j l
    have h := rationalWordWidth_of_height (GeneralPaperNativeUnitSourceJoin.height model.rat (fun w => w) W
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) (ownBudget m k b reciprocal)
      (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) _ _
      (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal) (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal) j l)
    exact h.trans (by unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight;omega)
  have hData : result.1.1=columns.1 := rfl
  have hShape : result.2=rows.2+columns.2+64*W := rfl
  refine ⟨GeneralPaperRetainedSourceColumnCallerStorage.bounded W k Qv R _ _ rows columns result hRows hColumns hData hP hQ hShape,?_⟩
  change result.2≤_
  rw [hShape]
  exact Nat.add_le_add_right (Nat.add_le_add hP hQ) _

def AtBound (old : ℕ → Prop) (columns limit : ℕ) : Prop := GeneralPaperSourceRowsCallerStorage.AtBound old columns limit

theorem bound_mono (old : ℕ → Prop) (columns B C : ℕ) (hBC : B≤C) (h : AtBound old columns B) :
    AtBound old columns C := GeneralPaperSourceRowsCallerStorage.bound_mono old columns B C hBC h

theorem retained_columns (old : ℕ → Prop) (owners columns limit : ℕ) (h : AtBound old columns limit)
    (hOwners : ∀ D,old D → owners≤D) : owners+columns≤limit :=
  GeneralPaperSourceRowsCallerStorage.retained_rows old owners columns limit h hOwners

theorem source_stage {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceColumnInputStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceBlockDivisionStorage.window model W m k)
        (GeneralPaperSourceLabelScatterStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizationParentStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceUnitCallerStorage.window model W k Qv weights b reciprocal))
        (GeneralPaperSourceRowsCallerStorage.window model W k Qv weights b reciprocal) bound)
        (window model W k Qv weights b reciprocal) (GeneralPaperSourceColumnCallerStorageRates.reservation model C d W m k Qv) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceRowsCallerStorage.source_stage hg W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex state inv
  exact ⟨GeneralPaperSourceRowsCallerStorageRates.reservation model C d W m k Qv,
    GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv,hOld,
    (source_column hg W k Qv weights hs b hb reciprocal hW hK hM hScatter).1,le_rfl⟩

theorem actual_reached {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hT : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)
        (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizedAnchorStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceRepresentativeSortStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceColumnInputStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceBlockDivisionStorage.window model W m k)
        (GeneralPaperSourceLabelScatterStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceQuantizationParentStorage.window model W k Qv weights b reciprocal)
        (GeneralPaperSourceUnitCallerStorage.window model W k Qv weights b reciprocal))
        (GeneralPaperSourceRowsCallerStorage.window model W k Qv weights b reciprocal) bound)
        (window model W k Qv weights b reciprocal) (GeneralPaperSourceColumnCallerStorageRates.reservation model C d W m k Qv) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceRowsCallerStorage.actual_reached hg W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceRowsCallerStorageRates.reservation model C d W m k Qv,
    GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv,hOld,
    (source_column hg W k Qv weights hs b hb reciprocal hW hK hM hScatter).1,le_rfl⟩

theorem guard_stage {m : ℕ} (model : RationalCostModel) (C d W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs+
      GeneralPaperSourceEndpointFractionConstructionStorage.window model W m k b+
      GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal+
      GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal+
      GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv+GeneralPaperSourceScoreStorage.profile model W m k+
      GeneralPaperScoreResidencyRates.initialProfile model W m k+GeneralPaperSourceScoreResidents.thresholdProfile model W m k+
      GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv+
      GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W m k+
      GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W m k+
      GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W m k+
      GeneralPaperSourceColumnInputStorageRates.sourceProfile model W m k+
      GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W m k+
      GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W m k+
      GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W m k+
      GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k+GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv+GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W m k Qv≤
        GeneralPaperSourceColumnCallerStorageRates.reservation model C d W m k Qv := by
  have hOld := GeneralPaperSourceRowsCallerStorage.guard_stage model C d W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceColumnCallerStorage
