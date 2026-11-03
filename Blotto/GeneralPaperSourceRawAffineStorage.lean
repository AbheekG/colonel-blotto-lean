import Blotto.GeneralPaperSourceRawAffineStorageRates

/-! Both actual raw affine evaluations at a reached final source basis.
Original selected N/beta and the constructed unreduced endpoint fraction
derive every operand premise, before acceptance or nonzero tests. The
complete previous affine/basis/grid and earlier-stage reserves remain. -/
namespace Blotto.GeneralPaperSourceRawAffineStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def numeratorCap (m k : ℕ) : ℕ := GeneralPaperSourceBasisGridSize.auxiliaryBound m k+(prepare m k).qbar
def denominatorCap (m k N : ℕ) : ℕ := N+(prepare m k).qbar

theorem width_bound (H B N : ℕ) : GeneralPaperRawAffineBits.width H B N≤32*(binaryWordWidth N+binaryWordWidth B+binaryWordWidth H+1) := by
  have h1 := GeneralPaperRayOperandWidthEnvelope.word_add 1 N
  have h2 := GeneralPaperRayOperandWidthEnvelope.word_add (1+N) B
  have h3 := GeneralPaperRayOperandWidthEnvelope.word_add (1+N+B) H
  have h4 := GeneralPaperRayOperandWidthEnvelope.word_add (1+N+B+H) ((N+B)*H)
  have h5 := GeneralPaperRayOperandWidthEnvelope.word_add N B
  have h6 := binaryWordWidth_mul (N+B) H
  have hOne : binaryWordWidth 1=1 := by decide
  unfold GeneralPaperRawAffineBits.width GeneralPaperRawAffineBits.cap
  omega

theorem source_width (m k N : ℕ) (hN : binaryWordWidth N≤GeneralPaperSourceRayStorageWidth.gridWord m k) :
    GeneralPaperRawAffineBits.width (prepare m k).H (numeratorCap m k) (denominatorCap m k N)≤
      GeneralPaperSourceRawAffineStorageRates.operandWidth m k := by
  have h := width_bound (prepare m k).H (numeratorCap m k) (denominatorCap m k N)
  have hB := GeneralPaperRayOperandWidthEnvelope.word_add (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (prepare m k).qbar
  have hD := GeneralPaperRayOperandWidthEnvelope.word_add N (prepare m k).qbar
  have hAux := GeneralPaperRayOperandWidthEnvelope.auxiliary_width m k
  unfold numeratorCap denominatorCap at h ⊢
  unfold GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperSourceRayStorageWidth.width
    GeneralPaperSourceRayStorageWidth.rootWidth GeneralPaperSourceRayStorageWidth.gridWord
  unfold GeneralPaperSourceRayStorageWidth.gridWord at hN
  omega

noncomputable def window {T m : ℕ} (model : RationalCostModel) (W k auxCopied endCopied : ℕ) (b : ℝ) (reciprocal : Bool)
    (_prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : ℕ :=
  let cache := GeneralPaperBasisAffineBits.prepare model.rat W state
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
    (GeneralPaperProxyClassifier.classify m k b)).1
  GeneralPaperRawAffineStorage.window model W auxCopied cache inputs.betaN inputs.controls.N+
    GeneralPaperRawAffineStorage.window model W endCopied cache (GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal)
      (GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal)

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve rawReserve,GeneralPaperSourceBasisAffineStorage.AtBound model W k previousReserve prep inputs state ∧
    (∀ auxCopied endCopied,window model W k auxCopied endCopied b reciprocal prep inputs state≤rawReserve) ∧
      previousReserve+rawReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hRaw,hSum⟩ := h
  exact ⟨D,F,hPrevious,hRaw,hSum.trans hBC⟩

theorem simultaneous {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∃ previousReserve,GeneralPaperSourceBasisAffineStorage.AtBound model W k previousReserve prep inputs state ∧
      ∀ a e B,B≤previousReserve → B+window model W k a e b reciprocal prep inputs state≤limit := by
  obtain ⟨D,F,hPrevious,hRaw,hSum⟩ := h
  exact ⟨D,hPrevious,fun a e B hB => (Nat.add_le_add hB (hRaw a e)).trans hSum⟩

theorem retained_affine {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ c s ac bs a e,GeneralPaperSourceBasisAffineStorage.window model W k c s ac bs prep inputs state+
      window model W k a e b reciprocal prep inputs state≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hAffine,hOldSum⟩,hRaw,hSum⟩ := h
  intro c s ac bs a e
  exact (Nat.add_le_add ((hAffine c s ac bs).trans (show F0≤D by omega)) (hRaw a e)).trans hSum

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceRawAffineStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let cache := GeneralPaperBasisAffineBits.prepare model.rat W state
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
    (GeneralPaperProxyClassifier.classify m k b)).1
  let B := numeratorCap m k
  let N := denominatorCap m k inputs.controls.N
  let R := GeneralPaperSourceRawAffineStorageRates.operandWidth m k
  have hOld := GeneralPaperSourceBasisAffineStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  have hOut := GeneralPaperBasisAffineBits.invariant_output model.rat W hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid state inv
  have hPow := GeneralPaperBasisCacheSize.power_H m k (m*((prepare m k).K-1)) le_rfl
  have hDet : cache.determinant.natAbs≤(prepare m k).H := hOut.1.trans hPow
  have hc (i) : (cache.constant.read i).natAbs≤(prepare m k).H := (hOut.2 i).1.trans hPow
  have hs' (i) : (cache.slope.read i).natAbs≤(prepare m k).H := (hOut.2 i).2.trans hPow
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  change inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k at hBeta
  have hEnd := GeneralPaperRetainedEndpointBitBounds.transformed_bounds model.rat W m k b hb hModify reciprocal
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hR : GeneralPaperRawAffineBits.width (prepare m k).H B N≤R := source_width m k inputs.controls.N hGridWord
  refine ⟨GeneralPaperSourceBasisAffineStorageRates.reservation model W m k,
    GeneralPaperSourceRawAffineStorageRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  intro a e
  have hA := GeneralPaperRawAffineStorage.bounded model W a (prepare m k).H B N R cache inputs.betaN inputs.controls.N
    (hBeta.trans (Nat.le_add_right _ _)) (Nat.le_add_right _ _) hDet hc hs' hR hW hDim
  have hE := GeneralPaperRawAffineStorage.bounded model W e (prepare m k).H B N R cache
    (GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal) (GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal)
    (hEnd.1.trans (Nat.le_add_left _ _)) (hEnd.2.trans (Nat.le_add_left _ _)) hDet hc hs' hR hW hDim
  change window model W k a e b reciprocal prep inputs state≤GeneralPaperSourceRawAffineStorageRates.sourceProfile model W m k
  unfold window GeneralPaperSourceRawAffineStorageRates.sourceProfile
  dsimp only
  dsimp only [cache,endpoint,B,N,R] at hA hE
  omega

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
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
      AtBound model W k (GeneralPaperSourceRawAffineStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hW hK hM hIndex hDim hBatch hFinalIndex state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceRawAffineStorage
