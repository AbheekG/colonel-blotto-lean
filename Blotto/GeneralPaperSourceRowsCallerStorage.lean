import Blotto.GeneralPaperSourceRowsCallerStorageRates

/-! Actual retained geometric source and rational-row caller, summed with
all earlier native unit-source and strict/endpoint contracts. The same
full pre-update trajectories and source-returned row IDs remain in use. -/
namespace Blotto.GeneralPaperSourceRowsCallerStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) : ℕ :=
  GeneralPaperRetainedSourceRowsCallerStorage.window model W k Qv (alphabet m k)
    (GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv) rfl weights
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)

theorem retained_rows_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (shared : GeneralPaperCatalogueShared.Shared m)
    (hs : shared=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (GeneralPaperRetainedSourceRows.run true model W k Qv (alphabet m k) c hc weights _ _ shared hs hT).1.1=
      GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal := by
  rw [GeneralPaperRetainedSourceRows.data]
  exact GeneralPaperSourceRowsDriver.rational_data true model W k Qv (prepare m k).qbar (alphabet m k) c hc weights _ _ shared hs

theorem source_rows {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    window model W k Qv weights b reciprocal≤GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv := by
  let a := alphabet m k
  let Bc := ownBudget m k b reciprocal
  let Br := opposingBudget m k b reciprocal
  let c := GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv
  let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
  have hBc := GeneralPaperSourceBudgetWidths.own_height m k b hb reciprocal
  have hBr := GeneralPaperSourceBudgetWidths.opposing_height m k b hb reciprocal
  have hwBc := (GeneralPaperSourceBudgetWidths.own_word m k b hb reciprocal).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0)
  have hwBr := (GeneralPaperSourceBudgetWidths.opposing_word m k b hb reciprocal).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0)
  have hWork := GeneralPaperSourceRowsDriver.bit_work hg W k Qv (a.lambda+1) a c rfl weights Bc Br shared rfl hs hBc hwBc hwBr
  exact GeneralPaperRetainedSourceRowsCallerStorage.bounded model (GeneralPaperFastRationalMajorant.model C d)
    (GeneralPaperFastRationalMajorant.dominates hg) W k Qv (a.lambda+1)
    (GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv) a c rfl weights hs Bc Br hBc hBr hWork

theorem retained_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (hw : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (shared : GeneralPaperCatalogueShared.Shared m)
    (hs : shared=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (GeneralPaperRetainedSourceRows.run true model W k Qv (alphabet m k) c hc weights _ _ shared hs hT).2≤
      GeneralPaperSourceRowsCallerStorageRates.sourceWorkCap C d W m k Qv := by
  rw [GeneralPaperRetainedSourceRows.data]
  exact GeneralPaperSourceRowsDriver.bit_work hg W k Qv ((alphabet m k).lambda+1) (alphabet m k) c hc weights _ _ shared hs hw
    (GeneralPaperSourceBudgetWidths.own_height m k b hb reciprocal)
    ((GeneralPaperSourceBudgetWidths.own_word m k b hb reciprocal).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0))
    ((GeneralPaperSourceBudgetWidths.opposing_word m k b hb reciprocal).trans (GeneralPaperSourceBudgetWidths.leaf_word m k 0))

/-- Additive composition retains the exact prior physical ownership proposition. -/
def AtBound (old : ℕ → Prop) (rows limit : ℕ) : Prop :=
  ∃ D F,old D ∧ rows≤F ∧ D+F≤limit

theorem bound_mono (old : ℕ → Prop) (rows B C : ℕ) (hBC : B≤C) (h : AtBound old rows B) :
    AtBound old rows C := by
  obtain ⟨D,F,hOld,hRows,hSum⟩ := h
  exact ⟨D,F,hOld,hRows,hSum.trans hBC⟩

theorem retained_rows (old : ℕ → Prop) (owners rows limit : ℕ) (h : AtBound old rows limit)
    (hOwners : ∀ D,old D → owners≤D) : owners+rows≤limit := by
  obtain ⟨D,F,hOld,hRows,hSum⟩ := h
  exact (Nat.add_le_add (hOwners D hOld) hRows).trans hSum

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
      AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) (GeneralPaperSourceRowsCallerStorageRates.reservation model C d W m k Qv) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceUnitCallerStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex state inv
  exact ⟨GeneralPaperSourceUnitCallerStorageRates.reservation model W m k Qv,
    GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv,hOld,source_rows hg W k Qv weights hs b hb reciprocal,le_rfl⟩

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
      AtBound (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W k limit b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) (GeneralPaperSourceRowsCallerStorageRates.reservation model C d W m k Qv) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceUnitCallerStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceUnitCallerStorageRates.reservation model W m k Qv,
    GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv,hOld,source_rows hg W k Qv weights hs b hb reciprocal,le_rfl⟩

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
      GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k+GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W m k Qv≤
        GeneralPaperSourceRowsCallerStorageRates.reservation model C d W m k Qv := by
  have hOld := GeneralPaperSourceUnitCallerStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceRowsCallerStorage
