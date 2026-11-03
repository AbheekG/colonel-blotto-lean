import Blotto.GeneralPaperSourceFinalEndpointReturnRates

/-! Complete endpoint and continuation parent returns at actual source
states. Original source/final-invariant/Cramer facts discharge every cache,
raw fraction, full basis, work-field and optional-vector premise. Previous
raw/check/affine/basis/grid and all earlier-stage reserves remain. -/
namespace Blotto.GeneralPaperSourceFinalEndpointReturnStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperSourceFinalCheckStorage (endpointFraction)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

noncomputable def window {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : ℕ :=
  let cache := GeneralPaperBasisAffineBits.prepare model.rat W state
  let endpoint := endpointFraction model W m k b
  let num := GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal
  let den := GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal
  let gamma := if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  GeneralPaperRawEndpointReturnStorage.window model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
    inputs.controls.auxiliary gamma inputs.betaN num inputs.controls.N den cache+
    GeneralPaperBasisContinuationReturnStorage.window model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.auxiliary gamma inputs.betaN num inputs.controls.N den state

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve returnReserve,GeneralPaperSourceFinalCheckStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    window model W k b reciprocal prep inputs state≤returnReserve ∧ previousReserve+returnReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hReturns,hSum⟩ := h
  exact ⟨D,F,hPrevious,hReturns,hSum.trans hBC⟩

theorem retained_checks {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ a e,GeneralPaperSourceFinalCheckStorage.window model W k b reciprocal prep inputs state a e+
      window model W k b reciprocal prep inputs state≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hChecks,hOldSum⟩,hReturns,hSum⟩ := h
  intro a e
  exact (Nat.add_le_add ((hChecks a e).trans (show F0≤D by omega)) hReturns).trans hSum

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceFinalEndpointReturnRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let cache := GeneralPaperBasisAffineBits.prepare model.rat W state
  let endpoint := endpointFraction model W m k b
  let num := GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal
  let den := GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal
  let H := (prepare m k).H
  let B := GeneralPaperSourceRawAffineStorage.numeratorCap m k
  let N := GeneralPaperSourceRawAffineStorage.denominatorCap m k inputs.controls.N
  let R := GeneralPaperSourceFinalEndpointReturnRates.operandWidth m k
  have hOld := GeneralPaperSourceFinalCheckStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hDetNZ : cache.determinant≠0 := inv.nonzero
  have hOut := GeneralPaperBasisAffineBits.invariant_output model.rat W hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid state inv
  have hPow := GeneralPaperBasisCacheSize.power_H m k (m*((prepare m k).K-1)) le_rfl
  have hDet : cache.determinant.natAbs≤H := hOut.1.trans hPow
  have hc (i) : (cache.constant.read i).natAbs≤H := (hOut.2 i).1.trans hPow
  have hs' (i) : (cache.slope.read i).natAbs≤H := (hOut.2 i).2.trans hPow
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  change inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k at hBeta
  have hAN : inputs.betaN.natAbs≤B := hBeta.trans (Nat.le_add_right _ _)
  have hAD : inputs.controls.N≤N := Nat.le_add_right _ _
  have hEnd := GeneralPaperRetainedEndpointBitBounds.transformed_bounds model.rat W m k b hb hModify reciprocal
  have hEN : num.natAbs≤B := hEnd.1.trans (Nat.le_add_left _ _)
  have hED : den≤N := hEnd.2.trans (Nat.le_add_left _ _)
  have hValue : endpoint.value=(GeneralPaperProxyClassifier.classify m k b).choice.endpoint :=
    GeneralPaperRetainedEndpointFraction.actual_value model.rat W m k b
  have hDen : 0 < den := GeneralPaperRetainedBasisEndpoint.denominator_positive endpoint reciprocal _ hValue hGuard
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hAuxEq : (inputs.betaN:ℚ)/(inputs.controls.N:ℚ)=inputs.controls.auxiliary :=
    GeneralPaperBasisGridInputs.auxiliary_decode m H f.num f.den reciprocal hm (H_positive m k) hf.1 f.den_pos
  have hEndEq : (num:ℚ)/(den:ℚ)=(if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint) := GeneralPaperRetainedBasisEndpoint.represented endpoint reciprocal _ hValue
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hRaw : GeneralPaperRawAffineBits.width H B N≤R :=
    (GeneralPaperSourceRawAffineStorage.source_width m k inputs.controls.N hGridWord).trans (by
      unfold R GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceFinalCheckStorageRates.operandWidth
      omega)
  have hRoot := (GeneralPaperSourceFinalCheckStorage.source_widths m k inputs.controls.N (N*H) hGridWord le_rfl).1
  have hCache := GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv
  have hConstant (i) := GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv i false
  have hSlope (i) := GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv i true
  have hBasis := GeneralPaperEncodedBasisStorage.invariant_bound W k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state inv
  have hAffineR : GeneralPaperBasisAffineBits.width (m*((prepare m k).K-1)) H (m+1)≤R :=
    (GeneralPaperSourceBasisAffineStorage.operand_width m k).trans (by
      unfold R GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceFinalCheckStorageRates.operandWidth
        GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperSourceBasisAffineStorageRates.operandWidth
        GeneralPaperSourceBasisCacheStorageRates.operandWidth
      omega)
  have hF : cache.work≤GeneralPaperSourceFinalEndpointReturnRates.affinePrice model W m k := by
    have h := GeneralPaperBasisAffineBits.work model.rat model.monotone W H (m+1) hW hDim state hCache.2 hCache.1 hConstant hSlope
    exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hAffineR) W))
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  have hRawReturn := GeneralPaperRawEndpointReturnStorage.bounded model W H B N R
    (GeneralPaperSourceFinalEndpointReturnRates.affinePrice model W m k) hm prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold hThreshold
    inputs.controls.auxiliary _ inputs.betaN num inputs.controls.N den hN hDen hAuxEq hEndEq
    cache hDetNZ hDet hc hs' hF hAN hAD hEN hED hRaw hRoot hW hDim hK hM hIndex
  have hContinue := GeneralPaperBasisContinuationReturnStorage.bounded model W H B N R
    (GeneralPaperSourceFinalEndpointReturnRates.affinePrice model W m k) (GeneralPaperEncodedBasisStorage.paperProfile W m k)
    hm prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold inputs.controls.auxiliary _
    inputs.betaN num inputs.controls.N den hN hDen hAuxEq hEndEq state hBasis hDetNZ hDet hc hs' hF
    hAN hAD hEN hED hRaw hRoot hW hDim hK hM hIndex
  refine ⟨GeneralPaperSourceFinalCheckStorageRates.reservation model W m k,
    GeneralPaperSourceFinalEndpointReturnRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  change window model W k b reciprocal prep inputs state≤GeneralPaperSourceFinalEndpointReturnRates.sourceProfile model W m k
  unfold window GeneralPaperSourceFinalEndpointReturnRates.sourceProfile
  dsimp only
  dsimp only [R,cache,num,den,endpoint] at hRawReturn hContinue
  omega

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound model W k (GeneralPaperSourceFinalEndpointReturnRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceFinalEndpointReturnStorage
