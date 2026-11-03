import Blotto.GeneralPaperSourceStrictChildStorageRates
import Blotto.GeneralPaperRetainedSourceColumnBits

/-! Complete initial table, strict threshold scan and maximum/guard
child lifetime joins. Full old strict-parent/matrix/active-DP and preceding
source/endpoint residents coexist with independent new child cursors.
All premises follow actual source data; no source algorithm changes. -/
namespace Blotto.GeneralPaperSourceStrictChildStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open GeneralPaperSourceStrictChildWindows

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) : Prop :=
  ∃ D I H M,GeneralPaperSourceStrictConstructorStorage.AtBound model W k D b reciprocal prep inputs state resident parent columns values ∧
    InitialBound model W k I columns values ∧ ThresholdBound model W k H columns values own opposing ∧
    MaximumBound model W k M columns values own opposing ∧ D+I+H+M≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state resident parent columns values own opposing) :
    AtBound model W k C b reciprocal prep inputs state resident parent columns values own opposing := by
  obtain ⟨D,I,H,M,hOld,hInitial,hThreshold,hMaximum,hSum⟩ := h
  exact ⟨D,I,H,M,hOld,hInitial,hThreshold,hMaximum,hSum.trans hBC⟩

theorem retained_children {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (resident parent : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ)
    (h : AtBound model W k limit b reciprocal prep inputs state resident parent columns values own opposing) :
    ∀ count (hc : count≤(prepare m k).S+1) load (hl : load≤m) sum (hs : sum≤m),
      resident+parent+initialWindow model W k columns values count hc+
        GeneralPaperScoreResidentPhases.thresholdWindow model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
          (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing+
        GeneralPaperSourceGuardStorage.window model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
          (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing load hl sum hs≤limit := by
  obtain ⟨D,I,H,M,hOld,hInitial,hThreshold,hMaximum,hSum⟩ := h
  obtain ⟨D0,P0,M0,C0,⟨D1,R1,_,hResident,hResidentSum⟩,hParent,_,_,hOldSum⟩ := hOld
  intro count hc load hl sum hs
  have hi := hInitial count hc
  have hm := hMaximum load hl sum hs
  change GeneralPaperScoreResidentPhases.thresholdWindow model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing≤H at hThreshold
  omega

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
      AtBound model W k (GeneralPaperSourceStrictChildStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal) := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceStrictConstructorStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  have hC := GeneralPaperSourceStrictChildWindows.source_components model W k Qv hQv weights hp hs b hb reciprocal hW hK hM hIndex
  refine ⟨GeneralPaperSourceStrictConstructorStorageRates.reservation model W m k Qv,
    GeneralPaperScoreResidencyRates.initialProfile model W m k,GeneralPaperSourceScoreResidents.thresholdProfile model W m k,
    GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv,hOld,hC.1,hC.2.1,hC.2.2,?_⟩
  unfold GeneralPaperSourceStrictChildStorageRates.reservation GeneralPaperSourceStrictChildStorageRates.sourceProfile
  omega

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
      AtBound model W k (GeneralPaperSourceStrictChildStorageRates.reservation model W m k Qv) b reciprocal prep inputs state
        (GeneralPaperSourceEnclosingOwners.window model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceStrictConstructorStorage.parentWindow model W k Qv hQv weights hp hs b reciprocal)
        (GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal)
        (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
        (GeneralPaperInitializerPreparedPoint.ownBudget m k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget m k b reciprocal) := by
  obtain ⟨state,hr,hOld⟩ := GeneralPaperSourceStrictConstructorStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  have hC := GeneralPaperSourceStrictChildWindows.source_components model W k Qv hQv weights hp hs b hb reciprocal hW hK hM hIndex
  refine ⟨state,hr,GeneralPaperSourceStrictConstructorStorageRates.reservation model W m k Qv,
    GeneralPaperScoreResidencyRates.initialProfile model W m k,GeneralPaperSourceScoreResidents.thresholdProfile model W m k,
    GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv,hOld,hC.1,hC.2.1,hC.2.2,?_⟩
  unfold GeneralPaperSourceStrictChildStorageRates.reservation GeneralPaperSourceStrictChildStorageRates.sourceProfile
  omega

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
      GeneralPaperSourceGuardStorage.sourceProfile model W m k Qv≤
        GeneralPaperSourceStrictChildStorageRates.reservation model W m k Qv := by
  have hOld := GeneralPaperSourceStrictConstructorStorage.guard_stage model W k Qv _hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex
  unfold GeneralPaperSourceStrictChildStorageRates.reservation GeneralPaperSourceStrictChildStorageRates.sourceProfile
  omega

end Blotto.GeneralPaperSourceStrictChildStorage
