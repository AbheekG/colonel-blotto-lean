import Blotto.GeneralPaperSourceFinalCheckStorageRates

/-! Both final native static/strict-score checks on the actual raw affine
candidate points. Raw lattices and magnitude caps hold before acceptance;
the existing reciprocal-zero guard supplies the endpoint denominator.
Complete previous raw/affine/basis/grid and earlier-stage reserves remain. -/
namespace Blotto.GeneralPaperSourceFinalCheckStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection GeneralPaperRayRationalBound
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

theorem check_widths (m D X P G : ℕ) (hD : D≤G) (hX : X≤G) (hP : P≤G) :
    GeneralPaperRayUniformSize.width D 1 m X 0 P+1≤32*(binaryWordWidth (m+1)+binaryWordWidth G+1) ∧
      GeneralPaperCommonLatticeDPBits.width D (X+1) m≤32*(binaryWordWidth (m+1)+binaryWordWidth G+1) := by
  have hd := binaryWordWidth_mono hD
  have hx := binaryWordWidth_mono hX
  have hp := binaryWordWidth_mono hP
  have hOne : binaryWordWidth 1=1 := by decide
  have hXP := GeneralPaperRayOperandWidthEnvelope.word_add X P
  have hXP1 := GeneralPaperRayOperandWidthEnvelope.word_add (X+P) 1
  have hA := binaryWordWidth_mul (m+1) (X+P+1)
  have hAA := GeneralPaperRayOperandWidthEnvelope.double_one ((m+1)*(X+P+1))
  have hBB := GeneralPaperRayOperandWidthEnvelope.double_one (m+1)
  have hX1 := GeneralPaperRayOperandWidthEnvelope.word_add X 1
  have hM := binaryWordWidth_mul (m+1) (X+1)
  have hM1 := GeneralPaperRayOperandWidthEnvelope.word_add ((m+1)*(X+1)) 1
  constructor
  · unfold GeneralPaperRayUniformSize.width GeneralPaperRayUniformSize.interceptCap GeneralPaperRayUniformSize.slopeCap
      GeneralPaperRayAffineBound.rootWidth
    simp only [Nat.zero_add,Nat.mul_one]
    omega
  · unfold GeneralPaperCommonLatticeDPBits.width
    omega

theorem source_widths (m k N D : ℕ) (hN : binaryWordWidth N≤GeneralPaperSourceRayStorageWidth.gridWord m k)
    (hD : D≤GeneralPaperSourceRawAffineStorage.denominatorCap m k N*(prepare m k).H) :
    let B := GeneralPaperSourceRawAffineStorage.numeratorCap m k
    let Q := GeneralPaperSourceRawAffineStorage.denominatorCap m k N
    GeneralPaperRayUniformSize.width D 1 m ((Q+B)*(prepare m k).H) 0 B+1≤GeneralPaperSourceFinalCheckStorageRates.operandWidth m k ∧
      GeneralPaperCommonLatticeDPBits.width D ((Q+B)*(prepare m k).H+1) m≤GeneralPaperSourceFinalCheckStorageRates.operandWidth m k := by
  let B := GeneralPaperSourceRawAffineStorage.numeratorCap m k
  let Q := GeneralPaperSourceRawAffineStorage.denominatorCap m k N
  let G := GeneralPaperRawAffineBits.cap (prepare m k).H B Q
  let R := GeneralPaperSourceRawAffineStorageRates.operandWidth m k
  have hRaw := GeneralPaperSourceRawAffineStorage.source_width m k N hN
  change 1+4*binaryWordWidth G≤R at hRaw
  have hM : binaryWordWidth (m+1)≤R := by
    have h := GeneralPaperRayOperandWidthEnvelope.word_add m 1
    have ho : binaryWordWidth 1=1 := by decide
    unfold R GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperSourceRayStorageWidth.width
      GeneralPaperSourceRayStorageWidth.rootWidth GeneralPaperSourceRayStorageWidth.gridWord
    omega
  have hProd : Q*(prepare m k).H≤G := by
    have h := Nat.mul_le_mul_right (prepare m k).H (Nat.le_add_right Q B)
    unfold G GeneralPaperRawAffineBits.cap
    omega
  have hDCap : D≤G := hD.trans hProd
  have hX : (Q+B)*(prepare m k).H≤G := by unfold G GeneralPaperRawAffineBits.cap; omega
  have hB : B≤G := by unfold G GeneralPaperRawAffineBits.cap; omega
  have hw := check_widths m D ((Q+B)*(prepare m k).H) B G hDCap hX hB
  have hFinal : 32*(binaryWordWidth (m+1)+binaryWordWidth G+1)≤64*R := by omega
  exact ⟨hw.1.trans hFinal,hw.2.trans hFinal⟩

def auxiliaryPoint {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Variable m (prepare m k).K → ℚ :=
  reader (GeneralPaperRawAffineEvaluate.run true model W (GeneralPaperBasisAffineBits.prepare model.rat W state) inputs.betaN inputs.controls.N).1
noncomputable def endpointFraction (model : RationalCostModel) (W m k : ℕ) (b : ℝ) : Farey.Fraction :=
  (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k) (GeneralPaperProxyClassifier.classify m k b)).1
noncomputable def endpointPoint {m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Variable m (prepare m k).K → ℚ :=
  let f := endpointFraction model W m k b
  reader (GeneralPaperRawAffineEvaluate.run true model W (GeneralPaperBasisAffineBits.prepare model.rat W state)
    (GeneralPaperRetainedBasisEndpoint.numerator f reciprocal) (GeneralPaperRetainedBasisEndpoint.denominator f reciprocal)).1

noncomputable def window {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (a : GeneralPaperFinalPolytopeStorage.Phase T model W inputs.matrix (auxiliaryPoint model W k inputs state) (prepare m k).S)
    (e : GeneralPaperFinalPolytopeStorage.Phase T model W inputs.matrix (endpointPoint model W k b reciprocal state) (prepare m k).S) : ℕ :=
  GeneralPaperFinalPolytopeStorage.window model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold inputs.controls.auxiliary
    (auxiliaryPoint model W k inputs state) a+
    GeneralPaperFinalPolytopeStorage.window model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      (if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint)
      (endpointPoint model W k b reciprocal state) e

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve checkReserve,GeneralPaperSourceRawAffineStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    (∀ a e,window model W k b reciprocal prep inputs state a e≤checkReserve) ∧ previousReserve+checkReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hChecks,hSum⟩ := h
  exact ⟨D,F,hPrevious,hChecks,hSum.trans hBC⟩

theorem retained_raw {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ c d a e,GeneralPaperSourceRawAffineStorage.window model W k c d b reciprocal prep inputs state+
      window model W k b reciprocal prep inputs state a e≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hRaw,hOldSum⟩,hChecks,hSum⟩ := h
  intro c d a e
  exact (Nat.add_le_add ((hRaw c d).trans (show F0≤D by omega)) (hChecks a e)).trans hSum

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
      AtBound model W k (GeneralPaperSourceFinalCheckStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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
  let X := (N+B)*H
  let R := GeneralPaperSourceFinalCheckStorageRates.operandWidth m k
  have hOld := GeneralPaperSourceRawAffineStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify
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
  have hADPos := Nat.mul_pos hN (Int.natAbs_pos.mpr hDetNZ)
  have hEDPos := Nat.mul_pos hDen (Int.natAbs_pos.mpr hDetNZ)
  have hxA (a) : Bounded (inputs.controls.N*cache.determinant.natAbs) X (auxiliaryPoint model W k inputs state a) :=
    GeneralPaperRawAffineBits.bounded model W H B N cache inputs.betaN inputs.controls.N hN hDetNZ hAN hAD hc hs' (GeneralPaperBasisCoordinates.index a)
  have hxE (a) : Bounded (den*cache.determinant.natAbs) X (endpointPoint model W k b reciprocal state a) :=
    GeneralPaperRawAffineBits.bounded model W H B N cache num den hDen hDetNZ hEN hED hc hs' (GeneralPaperBasisCoordinates.index a)
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hAuxEq : (inputs.betaN:ℚ)/(inputs.controls.N:ℚ)=inputs.controls.auxiliary :=
    GeneralPaperBasisGridInputs.auxiliary_decode m H f.num f.den reciprocal hm (H_positive m k) hf.1 f.den_pos
  have hbA := GeneralPaperRawAffineBits.threshold_bounded inputs.betaN inputs.controls.N hN cache.determinant.natAbs B hAN
  rw [hAuxEq] at hbA
  have hEndEq : (num:ℚ)/(den:ℚ)=(if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint) := GeneralPaperRetainedBasisEndpoint.represented endpoint reciprocal _ hValue
  have hbE := GeneralPaperRawAffineBits.threshold_bounded num den hDen cache.determinant.natAbs B hEN
  rw [hEndEq] at hbE
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hwA := source_widths m k inputs.controls.N (inputs.controls.N*cache.determinant.natAbs) hGridWord (Nat.mul_le_mul hAD hDet)
  have hwE := source_widths m k inputs.controls.N (den*cache.determinant.natAbs) hGridWord (Nat.mul_le_mul hED hDet)
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  have hScores : ∀ a l,((inputs.matrix.read a).read l).1≤(prepare m k).S := by
    intro a l
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
    simp only [FixedArrayTable.read_ofFn]
    convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) a l using 1
    rfl
  refine ⟨GeneralPaperSourceRawAffineStorageRates.reservation model W m k,
    GeneralPaperSourceFinalCheckStorageRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  intro a e
  have hA := GeneralPaperFinalPolytopeStorage.bounded model W (inputs.controls.N*cache.determinant.natAbs) X B R hm hADPos
    prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold hScores hThreshold inputs.controls.auxiliary hbA
    (auxiliaryPoint model W k inputs state) hxA hwA.1 hwA.2 hW hK hM hIndex a
  have hE := GeneralPaperFinalPolytopeStorage.bounded model W (den*cache.determinant.natAbs) X B R hm hEDPos
    prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold hScores hThreshold _ hbE
    (endpointPoint model W k b reciprocal state) hxE hwE.1 hwE.2 hW hK hM hIndex e
  change window model W k b reciprocal prep inputs state a e≤GeneralPaperSourceFinalCheckStorageRates.sourceProfile model W m k
  unfold window GeneralPaperSourceFinalCheckStorageRates.sourceProfile
  dsimp only [R] at hA hE
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
      AtBound model W k (GeneralPaperSourceFinalCheckStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceFinalCheckStorage
