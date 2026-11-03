import Blotto.GeneralPaperSourceEnclosingOwnerRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Complete actual source rows, native physical columns, original
prepared strict table, matrix and scalar return ownership. Exact native
column and prepared identities supply every payload premise. The new
resident window SUMS with all preceding native endpoint/source reserves;
constructor/caller scratch and original value/input owners remain open. -/
namespace Blotto.GeneralPaperSourceEnclosingOwners
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

noncomputable def columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ)
    (b : ℝ) (reciprocal : Bool) :=
  (GeneralPaperNativeUnitSourceJoin.run model.rat (fun w => w) W
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)).1

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) : ℕ :=
  GeneralPaperEnclosingSourceOwners.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal)
    (columns model W k Qv weights b reciprocal) (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)

theorem column_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℝ) (reciprocal : Bool) :
    GeneralPaperRowQuantizer.dictionary (columns model W k Qv weights b reciprocal)=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal :=
  GeneralPaperNativeUnitSourceJoin.data _ _ _ _ _ _ _ _

theorem literal_columns {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℝ) (reciprocal : Bool)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m (alphabet m k).lambda k Qv)
    (shared : GeneralPaperCatalogueShared.Shared m)
    (hs : shared=GeneralPaperCatalogueShared.prepare (alphabet m k) k Qv weights
      (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal))
    (hT : shared.trajectory.rows=(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows) :
    (GeneralPaperRetainedSourceColumnBits.run model W k Qv (alphabet m k) c hc weights _ _ shared hs hT
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)).1.1=
        columns model W k Qv weights b reciprocal := by
  apply GeneralPaperRetainedBitData.dictionary_injective
  exact (GeneralPaperRetainedSourceColumnBits.data model W k Qv (prepare m k).qbar (alphabet m k) c hc weights _ _ shared hs hT _ _ _).trans
    (column_data model W k Qv weights b reciprocal).symm

theorem prepared_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    let cols := columns model W k Qv weights b reciprocal
    let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let out := (GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) cols values
      (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal)).1
    out.prepared=prep ∧ out.matrix=(GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal).matrix := by
  have hc := column_data model W k Qv weights b reciprocal
  have hv := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  exact ⟨GeneralPaperSourceStrictPreparationBits.actual_prepared model W k Qv hQv weights hp hs b reciprocal _ _ hc hv,
    GeneralPaperSourceStrictPreparationBits.actual_matrix model W k Qv hQv weights hp hs b reciprocal _ _ hc hv⟩

theorem source_owners {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    window model W k Qv hQv weights hp hs b reciprocal≤GeneralPaperSourceEnclosingOwnerRates.sourceProfile model W m k := by
  let cols := columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let own := GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal
  let opposing := GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal
  let out := (GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) cols values own opposing).1
  let A := GeneralPaperSourceScoreHeights.anchorHeight m k
  have hColumns := column_data model W k Qv weights b reciprocal
  have hValues := GeneralPaperRetainedFieldValues.selector_data true model W Qv hQv weights hp hs
  have ha (j l) : RationalHeight ((cols.read j).anchors.read l) A := by
    change RationalHeight ((GeneralPaperRowQuantizer.dictionary cols).anchor j l) A
    rw [hColumns,GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
    exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
  have hTable := GeneralPaperSourceScoreStorage.table_return model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S A (GeneralPaperScoreScaleParameters.labels_positive m k) cols values own opposing
    (GeneralPaperScoreScaleParameters.score_cap m k) ha
  have hMat := GeneralPaperSourceStrictPreparationBits.actual_matrix model W k Qv hQv weights hp hs b reciprocal cols values hColumns hValues
  have hMatrix : GeneralPaperEncodedScoreMatrixStorage.matrixFootprint W out.matrix≤GeneralPaperSourceInitializerReturnStorageRates.matrixProfile W m k := by
    apply GeneralPaperEncodedScoreMatrixStorage.matrix_bound (K:=(prepare m k).K)
    · intro j l
      rw [hMat]
      erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
        (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
      simp only [FixedArrayTable.read_ofFn]
      convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) j l using 1
      rfl
    · intro j l
      rw [hMat]
      erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
        (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
      simpa only [FixedArrayTable.read_ofFn] using GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
  have hMatrixCap : GeneralPaperSourceInitializerReturnStorageRates.matrixProfile W m k≤GeneralPaperSourceInitializerReturnStorageRates.sourceProfile model W m k := by
    unfold GeneralPaperSourceInitializerReturnStorageRates.sourceProfile GeneralPaperRetainedInputsReturnStorage.profile
    omega
  have hBudget := rationalWordWidth_of_height ((GeneralPaperSourceStrictPreparationBits.opposing_height m k b hb reciprocal).div
    (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal))
  exact GeneralPaperEnclosingSourceOwners.bounded model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (1+2*A) (GeneralPaperScoreBitPrimitive.resourceWidth A m) (1+4*binaryWordWidth (prepare m k).qbar)
    (GeneralPaperSourceInitializerReturnStorageRates.sourceProfile model W m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperSourceInitializer.sourceRows k Qv weights b reciprocal) cols values own opposing
    (fun i j => (rationalWordWidth_of_height (GeneralPaperSourceScoreHeights.rows_height k Qv weights b reciprocal i j)).trans
      (by unfold A GeneralPaperSourceScoreHeights.anchorHeight; omega))
    (fun j l => rationalWordWidth_of_height (ha j l)) hTable (hMatrix.trans hMatrixCap)
    (GeneralPaperSourceStrictPreparationBits.threshold_bound model W _ _ _ cols values own opposing)
    (GeneralPaperSourceStrictPreparationBits.maximum_bound model W _ _ _ cols values own opposing (GeneralPaperScoreScaleParameters.score_cap m k))
    (by change rationalWordWidth (opposing/own)≤_ at hBudget ⊢; omega)

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (ownerWindow : ℕ) : Prop :=
  ∃ previousReserve returnReserve,GeneralPaperSourceEndpointFractionConstructionStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    ownerWindow≤returnReserve ∧ previousReserve+returnReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (ownerWindow B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state ownerWindow) : AtBound model W k C b reciprocal prep inputs state ownerWindow := by
  obtain ⟨D,F,hPrevious,hReturns,hSum⟩ := h
  exact ⟨D,F,hPrevious,hReturns,hSum.trans hBC⟩

theorem retained_outer {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (ownerWindow : ℕ)
    (h : AtBound model W k limit b reciprocal prep inputs state ownerWindow) :
    GeneralPaperSourceEndpointFractionConstructionStorage.window model W m k b+
      ownerWindow≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hPacking,hOldSum⟩,hReturns,hSum⟩ := h
  exact (Nat.add_le_add (hPacking.trans (show F0≤D by omega)) hReturns).trans hSum

theorem source_guard {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (_hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    GeneralPaperSourceOuterEndpointStorage.window model W k b reciprocal prep inputs+
      GeneralPaperSourceEndpointFractionConstructionStorage.window model W m k b+window model W k Qv hQv weights hp hs b reciprocal≤
        GeneralPaperSourceEnclosingOwnerRates.reservation model W m k := by
  have hOld := GeneralPaperSourceEndpointFractionConstructionStorage.source_guard model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard
  have hNew := source_owners model W k Qv hQv weights hp hs b hb reciprocal
  exact Nat.add_le_add hOld hNew

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceEnclosingOwnerRates.reservation model W m k) b reciprocal prep inputs state (window model W k Qv hQv weights hp hs b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceEndpointFractionConstructionStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  exact ⟨GeneralPaperSourceEndpointFractionConstructionStorageRates.reservation model W m k,
    GeneralPaperSourceEnclosingOwnerRates.sourceProfile model W m k,hOld,
    source_owners model W k Qv hQv weights hp hs b hb reciprocal,le_rfl⟩

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound model W k (GeneralPaperSourceEnclosingOwnerRates.reservation model W m k) b reciprocal prep inputs state (window model W k Qv hQv weights hp hs b reciprocal) := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hStart := GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperBasisControllerSound.stages_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S prep.threshold inputs.controls.N hN
    (GeneralPaperScoreScaleParameters.score_cap m k) inputs.betaN inputs.initialGrid (hStart) (m*((prepare m k).K-1)) le_rfl
  have hReturn : GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl=some state := by
    rw [GeneralPaperSharedBasisInputs.matrix_eq]; exact hr
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hFinalIndex state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceEnclosingOwners
