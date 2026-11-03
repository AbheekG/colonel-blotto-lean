import Blotto.GeneralPaperSourceBasisAffineStorageRates

/-! Actual final reached basis and complete native affine preparation.
The final full basis, fixed grid and original N/beta remain owned. Earlier
stages retain their checked uniform phase contracts; whole basis states are
not summed over all stages. Actual controller returns are preserved. -/
namespace Blotto.GeneralPaperSourceBasisAffineStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

def window {T m : ℕ} (model : RationalCostModel) (W k cCopied sCopied acCopied bsCopied : ℕ)
    (_prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : ℕ :=
  GeneralPaperEncodedBasisStorage.footprint W state+arrayFootprint W integerBits inputs.initialGrid+
    natBits inputs.controls.N+integerBits inputs.betaN+
    GeneralPaperBasisAffineStorage.window model W cCopied sCopied acCopied bsCopied state

def EarlierAtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K) : Prop :=
  ∀ j (hj : j<m*((prepare m k).K-1)),∃ state,
    (GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      GeneralPaperSourceBasisAdvanceStorage.StageAtBound model W k limit prep inputs state hj

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve affineReserve,EarlierAtBound model W k previousReserve prep inputs ∧
    (∀ c s ac bs,window model W k c s ac bs prep inputs state≤affineReserve) ∧ previousReserve+affineReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B prep inputs state) : AtBound model W k C prep inputs state := by
  obtain ⟨D,F,hPrevious,hAffine,hSum⟩ := h
  exact ⟨D,F,hPrevious,hAffine,hSum.trans hBC⟩

theorem simultaneous {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit prep inputs state) :
    ∃ previousReserve,EarlierAtBound model W k previousReserve prep inputs ∧
      ∀ c s ac bs B,B≤previousReserve → B+window model W k c s ac bs prep inputs state≤limit := by
  obtain ⟨D,F,hPrevious,hAffine,hSum⟩ := h
  exact ⟨D,hPrevious,fun c s ac bs B hB => (Nat.add_le_add hB (hAffine c s ac bs)).trans hSum⟩

theorem retained_stage {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (finalState : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit prep inputs finalState) (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      ∃ answer,(GeneralPaperSourceBasisAdvanceStorage.endpoint model W k prep inputs state hj).1=some answer ∧
        ∀ p a c s ac bs,GeneralPaperSourceBasisAdvanceStorage.window model W k p a prep inputs state hj answer+
          window model W k c s ac bs prep inputs finalState≤limit := by
  obtain ⟨D,F,hPrevious,hAffine,hSum⟩ := h
  obtain ⟨state,hr,⟨D0,F0,_,⟨answer,ha,hAdvance⟩,hOldSum⟩⟩ := hPrevious j hj
  exact ⟨state,hr,answer,ha,fun p a c s ac bs =>
    (Nat.add_le_add ((hAdvance p a).trans (show F0≤D by omega)) (hAffine c s ac bs)).trans hSum⟩

theorem operand_width (m k : ℕ) :
    GeneralPaperBasisAffineBits.width (m*((prepare m k).K-1)) (prepare m k).H (m+1)≤
      GeneralPaperSourceBasisAffineStorageRates.operandWidth m k := by
  let d := m*((prepare m k).K-1)
  have hc := GeneralPaperIntegerDotPrice.cap_bounds d (prepare m k).H (m+1)
  have hh := binaryWordWidth_mono hc.1
  have hm := binaryWordWidth_mono hc.2.1
  have hw := (GeneralPaperBasisCacheBitFacts.component_widths d (prepare m k).H (m+1)).1
  have h : GeneralPaperBasisAffineBits.width d (prepare m k).H (m+1)≤3*GeneralPaperBasisCacheBitFacts.width d (prepare m k).H (m+1) := by
    unfold GeneralPaperBasisAffineBits.width
    omega
  exact h.trans (Nat.mul_le_mul_left 3 (GeneralPaperSourceBasisCacheStorage.cache_width m k d le_rfl))

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceBasisAffineStorageRates.reservation model W m k) prep inputs state := by
  dsimp only
  intro state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let R := GeneralPaperSourceBasisAffineStorageRates.operandWidth m k
  have hCache := GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv
  have hConstant (i) := GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv i false
  have hSlope (i) := GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv i true
  have hBasis := GeneralPaperEncodedBasisStorage.invariant_bound W k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state inv
  have hGrid := GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  change inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k at hBeta
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hBudget := GeneralPaperSourceBasisCacheStorage.budget_width m k inputs.controls.N hGridWord
  have hBudgetR : GeneralPaperBasisBudgetBits.width inputs.controls.N (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)≤R :=
    hBudget.trans (by dsimp only [R]; unfold GeneralPaperSourceBasisAffineStorageRates.operandWidth; omega)
  have hNWord : natBits inputs.controls.N≤R := by unfold natBits GeneralPaperBasisBudgetBits.width at *; omega
  have hBWord : integerBits inputs.betaN≤R := by have h := binaryWordWidth_mono hBeta; unfold integerBits GeneralPaperBasisBudgetBits.width at *; omega
  have hGridOwner := GeneralPaperEncodedBasisStorage.array_bound W R integerBits inputs.initialGrid (by
    intro i; exact (Nat.add_le_add_left (binaryWordWidth_mono (hGrid i)) 1).trans hNWord)
  refine ⟨GeneralPaperSourceBasisAdvanceStorageRates.reservation model W m k,
    GeneralPaperSourceBasisAffineStorageRates.sourceProfile model W m k,?_,?_,le_rfl⟩
  · intro j hj
    exact GeneralPaperSourceBasisAdvanceStorage.actual_reached model W k Qv hm hQv weights hp hs b hb reciprocal
      hW hK hM hIndex hDim hBatch hFinalIndex j hj
  · intro c s ac bs
    have hAffine := GeneralPaperBasisAffineStorage.bounded model W c s ac bs (prepare m k).H (m+1) R state
      hCache.2 hCache.1 hConstant hSlope (operand_width m k) hW hDim
    change window model W k c s ac bs prep inputs state≤GeneralPaperSourceBasisAffineStorageRates.sourceProfile model W m k
    unfold window GeneralPaperSourceBasisAffineStorageRates.sourceProfile
    dsimp only
    dsimp only [R] at hAffine hGridOwner hNWord hBWord
    omega

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
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
      AtBound model W k (GeneralPaperSourceBasisAffineStorageRates.reservation model W m k) prep inputs state := by
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
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch hFinalIndex state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceBasisAffineStorage
