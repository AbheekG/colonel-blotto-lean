import Blotto.GeneralPaperSourceUnitCallerStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Actual native unit-source caller on the same retained source rows
and proxy own-budget as quantization/normalization. Native source heights
and actual checked child work derive every full physical owner/counter;
this caller reserve SUMS with all earlier native source/strict contracts. -/
namespace Blotto.GeneralPaperSourceUnitCallerStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) : ℕ :=
  GeneralPaperUnitSourceCallerStorage.window model W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)

theorem native_columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :
    (GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
      (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)).1=
        GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal := rfl

theorem retained_columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (shared : GeneralPaperCatalogueShared.Shared m)
    (hs : shared=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
      (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1.1=
        GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal :=
  GeneralPaperSourceEnclosingOwners.literal_columns model W k Qv weights b reciprocal c hc shared hs hT

theorem source_unit {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hScatter : binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+1)≤W) :
    window model W k Qv weights b reciprocal≤GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k ∧
      (GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
        (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)).2≤
          GeneralPaperUnitSourceCallerStorage.price W (GeneralPaperSourceUnitCallerStorageRates.quantizationPrice model W m k)
            (GeneralPaperSourceUnitCallerStorageRates.normalizationPrice model W m k) := by
  let rows := GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal
  let budget := GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal
  let old := GeneralPaperSourceDictionaryNormalizationStorage.quantized model W k Qv weights b reciprocal
  let result := GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) budget rows
  let R := GeneralPaperSourceUnitCallerStorageRates.operandWidth m k
  have hBudget := GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal
  have hRowsHeight := GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal
  have hOldHeight (j l) := GeneralPaperNativeUnitSourceJoin.quantized_height model.rat (fun w => w) W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) rows _ hRowsHeight j l
  have hNewHeight (j l) := GeneralPaperNativeUnitSourceJoin.height model.rat (fun w => w) W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) budget rows _ _ hBudget hRowsHeight j l
  have hbWord : rationalWordWidth budget≤R := by
    have h := rationalWordWidth_of_height hBudget
    unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    change rationalWordWidth budget≤_ at h
    omega
  have hRows (i j) : rationalWordWidth ((rows.read i).read j)≤R := by
    have h := rationalWordWidth_of_height (hRowsHeight i j)
    unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    change rationalWordWidth ((rows.read i).read j)≤_ at h
    omega
  have hOld : GeneralPaperEnclosingSourceOwners.columnsFoot W old≤GeneralPaperEnclosingSourceOwners.columnsProfile W
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K R := by
    apply GeneralPaperEnclosingSourceOwners.columns_bound W R
    intro j l
    have h := rationalWordWidth_of_height (hOldHeight j l)
    unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    change rationalWordWidth ((old.read j).anchors.read l)≤_ at h
    omega
  have hNew : GeneralPaperEnclosingSourceOwners.columnsFoot W result.1≤GeneralPaperEnclosingSourceOwners.columnsProfile W
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K R := by
    apply GeneralPaperEnclosingSourceOwners.columns_bound W R
    intro j l
    have h := rationalWordWidth_of_height (hNewHeight j l)
    unfold R GeneralPaperSourceUnitCallerStorageRates.operandWidth GeneralPaperSourceScoreHeights.anchorHeight
    change rationalWordWidth ((result.1.read j).anchors.read l)≤_ at h
    omega
  have hP := (GeneralPaperSourceQuantizationParentStorage.source_parents model W k Qv weights b reciprocal hW hK hM hScatter).2
  have hQ := (GeneralPaperSourceDictionaryNormalizationStorage.source_normalization model W k Qv weights b hb reciprocal hW hK hM).2
  refine ⟨?_,?_⟩
  · exact GeneralPaperUnitSourceCallerStorage.bounded (K:=(prepare m k).K) model W R
      (GeneralPaperSourceUnitCallerStorageRates.quantizationPrice model W m k) (GeneralPaperSourceUnitCallerStorageRates.normalizationPrice model W m k)
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) budget rows hbWord hRows hOld hNew hP hQ
  · exact GeneralPaperUnitSourceCallerStorage.work (K:=(prepare m k).K) model W
      (GeneralPaperSourceUnitCallerStorageRates.quantizationPrice model W m k) (GeneralPaperSourceUnitCallerStorageRates.normalizationPrice model W m k)
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) budget rows hP hQ

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ)
    (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (quantizationSpace : (outer : ℕ) → outer≤m → Option (Fin m) → ℕ) (unitSpace : ℕ) : Prop :=
  ∃ D U,GeneralPaperSourceQuantizationParentStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace ∧
    unitSpace≤U ∧ D+U≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K)) (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ) (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ) (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ) (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ) (quantizationSpace : (outer : ℕ) → outer≤m → Option (Fin m) → ℕ) (unitSpace : ℕ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace unitSpace) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace unitSpace := by
  obtain ⟨D,U,hOld,hUnit,hSum⟩ := h
  exact ⟨D,U,hOld,hUnit,hSum.trans hBC⟩

theorem retained_unit {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (unnormalized : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (anchorSpace : Fin m → (count : ℕ) → count≤(prepare m k).K → ℕ)
    (sortSpace : Fin m → ℕ → ℕ → GeneralPaperSourceRepresentativeSortStorage.Active model W m k → ℕ)
    (materialSpace : Fin m → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → ℕ)
    (divisionSpace : Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (scatterSpace : Fin m → (initialCount : ℕ) → initialCount≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → (count : ℕ) → count≤(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows → Option (GeneralPaperSourceBlockDivisionStorage.Index model W m k) → ℕ)
    (quantizationSpace : (outer : ℕ) → outer≤m → Option (Fin m) → ℕ)
    (unitSpace : ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace unitSpace) :
    ∀ j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter outer ho field,
      resident+parent+anchorSpace j count hc+sortSpace l used copied active+materialSpace p fill hf+divisionSpace division+
        scatterSpace q initialCount hi scatterCount hs scatter+quantizationSpace outer ho field+unitSpace≤limit := by
  obtain ⟨D,U,hOld,hUnit,hSum⟩ := h
  have hPrevious := GeneralPaperSourceQuantizationParentStorage.retained_parents model W k D b reciprocal prep inputs state resident parent columns values own opposing unnormalized anchorSpace sortSpace materialSpace divisionSpace scatterSpace quantizationSpace hOld
  intro j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter outer ho field
  have hp := hPrevious j count hc l used copied active p fill hf division q initialCount hi scatterCount hs scatter outer ho field
  omega

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
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
      AtBound model W k (GeneralPaperSourceUnitCallerStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceQuantizationParentStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex state inv
  exact ⟨GeneralPaperSourceQuantizationParentStorageRates.reservation model W m k Qv,
    GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k,hOld,(source_unit model W k Qv weights b hb reciprocal hW hK hM hScatter).1,le_rfl⟩

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
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
      AtBound model W k (GeneralPaperSourceUnitCallerStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
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
        (window model W k Qv weights b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceQuantizationParentStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hT hScatter hFinalIndex
  exact ⟨state,hr,GeneralPaperSourceQuantizationParentStorageRates.reservation model W m k Qv,
    GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k,hOld,(source_unit model W k Qv weights b hb reciprocal hW hK hM hScatter).1,le_rfl⟩

theorem guard_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
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
      GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W m k≤
        GeneralPaperSourceUnitCallerStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceQuantizationParentStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  exact Nat.add_le_add_right hOld _

end Blotto.GeneralPaperSourceUnitCallerStorage
