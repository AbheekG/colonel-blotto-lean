import Blotto.GeneralPaperRetainedModifiedColumnStorage

/-! The actual optional native endpoint owns the already checked compact
point profile, rather than the full enclosing basis lifetime. This derives
each materialized rational payload bound, including zero/rejection paths. -/
namespace Blotto.GeneralPaperSourceModifiedColumnPointBounds
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperEncodedScalarStorage
open GeneralPaperInitializerPreparedPoint
open GeneralPaperSourceFinalCheckStorage (endpointFraction)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def pointProfile (W m k : ℕ) : ℕ := GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile W m k
def gammaWidth (m k : ℕ) : ℕ := GeneralPaperSourceEndpointScalarStorageRates.operandWidth m k
def resultProfile (W m k : ℕ) : ℕ := pointProfile W m k+gammaWidth m k+64*W+2

theorem positive_point_profile (W m k : ℕ) : 1≤pointProfile W m k := by
  unfold pointProfile GeneralPaperSourceEndpointContinuationReturnBounds.pointProfile GeneralPaperRawEndpointReturnStorage.optionProfile
  omega

theorem raw_point {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    GeneralPaperRawEndpointReturnStorage.optionFoot W (GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H f.num f.den reciprocal
      prep inputs.matrix (endpointFraction model W m k b) (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).1≤pointProfile W m k := by
  dsimp only
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let endpoint := endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  by_cases hGuard : reciprocal=true ∧ value=0
  · rw [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_left hGuard]
    exact positive_point_profile W m k
  · have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
    have hInput := GeneralPaperRetainedBasisInputs.actual_data true model W k f.num f.den reciprocal prep v inputs.matrix
      (GeneralPaperSharedBasisInputs.matrix_eq k prep v f.num f.den reciprocal) hm hf.1 f.den_pos
    obtain ⟨state,hReturn,inv,_⟩ := GeneralPaperSharedBasisBits.actual_return model W k Qv hm hQv weights hp hs b hb reciprocal
      hW hDim hIndex hBatch hFinal
    have hDim1 := (binaryWordWidth_mono (show m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3 by omega)).trans hDim
    have hPoint := (GeneralPaperSourceEndpointContinuationReturnBounds.source_bounds model W k Qv hm hQv weights hp hs b hb reciprocal
      hModify hGuard hW hK hM hIndex hDim1 state inv).2.1
    rw [GeneralPaperRetainedBasisEndpointBits.run,ite_eq_right hGuard]
    dsimp only
    rw [hInput,hReturn]
    exact hPoint

theorem branch_result {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    GeneralPaperRetainedCompilerBranchStorage.resultFoot W (GeneralPaperSourceCompilerBranchStorage.run model W k Qv hQv weights hp hs b reciprocal).1≤
      resultProfile W m k := by
  let columns := GeneralPaperSourceEnclosingOwners.columns model W k Qv weights b reciprocal
  let values := (GeneralPaperRetainedFieldValues.run true model W Qv hQv weights hp hs).1
  let own := ownBudget m k b reciprocal
  let opposing := opposingBudget m k b reciprocal
  let retained := GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let endpoint := endpointFraction model W m k b
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let reached := GeneralPaperRetainedCompilerBranchStorage.child model W (prepare m k).H f.num f.den reciprocal endpoint value retained
  have hData := GeneralPaperSourceEnclosingOwners.prepared_data model W k Qv hQv weights hp hs b reciprocal
  change retained.1.prepared=prep ∧ retained.1.matrix=inputs.matrix at hData
  have hRaw := raw_point model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinal
  have hReached : GeneralPaperRawEndpointReturnStorage.optionFoot W reached.1≤pointProfile W m k := by
    unfold reached GeneralPaperRetainedCompilerBranchStorage.child
    split
    · exact positive_point_profile W m k
    · rw [hData.1,hData.2]
      exact hRaw
  have hValue := GeneralPaperEndpointRatioSize.height m k b hb hModify
  change RationalHeight value (binaryWordWidth (prepare m k).qbar) at hValue
  have hGamma : rationalWordWidth (if reciprocal then 1/value else value)≤gammaWidth m k := by
    have hOne : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
    cases reciprocal with
    | false => exact (rationalWordWidth_of_height hValue).trans (by unfold gammaWidth GeneralPaperSourceEndpointScalarStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth;omega)
    | true => exact (rationalWordWidth_of_height (hOne.div hValue)).trans (by unfold gammaWidth GeneralPaperSourceEndpointScalarStorageRates.operandWidth GeneralPaperRetainedEndpointBitBounds.priceWidth;omega)
  exact (GeneralPaperRetainedCompilerBranchStorage.result_bound model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (prepare m k).H f.num f.den (GeneralPaperScoreScaleParameters.labels_positive m k) columns values own opposing reciprocal endpoint value).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hReached hGamma) _) _)

theorem choice {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W)
    (result : GeneralPaperSourceEndpointBranch.Result (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (hr : (GeneralPaperSourceCompilerBranchStorage.run model W k Qv hQv weights hp hs b reciprocal).1=some result) :
    GeneralPaperRetainedCompilerBranchStorage.choiceFoot W result.choice≤resultProfile W m k := by
  have h := branch_result model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinal
  rw [hr] at h
  simp only [GeneralPaperRetainedCompilerBranchStorage.resultFoot] at h
  exact (show GeneralPaperRetainedCompilerBranchStorage.choiceFoot W result.choice≤
    1+GeneralPaperRetainedCompilerBranchStorage.choiceFoot W result.choice+32*W by omega).trans h

end Blotto.GeneralPaperSourceModifiedColumnPointBounds
