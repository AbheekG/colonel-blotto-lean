import Blotto.GeneralPaperSourceParametricCallerRates

/-! Actual reached-source caller/return composition. The preceding phase
contract retains every original data owner; a separate simultaneous caller
reserve covers all recursive outputs/frames plus one active stage caller.
The two reserves add before the literal common-word bound is applied. -/
namespace Blotto.GeneralPaperSourceEndpointCallerStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def CallersAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W inputs.matrix x w).1
  ∃ c,(GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c ∧
    let loop := GeneralPaperParametricRunStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) fields 0 c.time
    loop≤limit ∧ GeneralPaperRayGenerationCoverage.high model W inputs.matrix x w (prepare m k).S prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) 0 c.time
      (fun field out => loop+GeneralPaperParametricStageCallerStorage.window model W inputs.matrix x w prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) field out.table out.bracket.lower out.bracket.upper≤limit) (fun _ => True)

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  ∃ dataReserve callerReserve,
    GeneralPaperSourceEndpointLayerStorage.StageAtBound model W k dataReserve prep inputs state hj ∧
      CallersAtBound model W k callerReserve prep inputs state hj ∧ dataReserve+callerReserve≤limit

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  obtain ⟨D,F,hData,hCallers,hSum⟩ := h
  exact ⟨D,F,hData,hCallers,hSum.trans hBC⟩

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      StageAtBound model W k (GeneralPaperSourceParametricCallerRates.reservation model W m k) prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let R := GeneralPaperRayUniformSize.width (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs
  let H := GeneralPaperSourceRayStorageWidth.width m k
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hCache := (GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv).1
  have hAux : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hRoot := GeneralPaperSourceRayStorageWidth.root_bound m k j b hb reciprocal state.determinant.natAbs inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux
  change R≤GeneralPaperSourceRayStorageWidth.rootWidth m k at hRoot
  have hRH : R≤H := by dsimp only [H]; unfold GeneralPaperSourceRayStorageWidth.width; omega
  have hScores : ∀ a l,((inputs.matrix.read a).read l).1≤(prepare m k).S := by
    intro a l
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
    simp only [FixedArrayTable.read_ofFn]
    convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) a l using 1
    rfl
  have hED : state.determinant.natAbs∣inputs.controls.N*state.determinant.natAbs :=
    ⟨inputs.controls.N,Nat.mul_comm _ _⟩
  have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  let fields := (GeneralPaperAffineInputPrice.run (fun w => w) W inputs.matrix x w).1
  have hFields : ∀ field∈fields,GeneralPaperRayAffineDPSize.FieldBounded (inputs.controls.N*state.determinant.natAbs)
      state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) field := by
    dsimp only [fields]
    rw [GeneralPaperAffineInputPrice.data]
    exact GeneralPaperRayAnchorBound.fields _ _ _ _ inputs.matrix x w hx hw
  have hLength : fields.length=m := by dsimp only [fields]; rw [GeneralPaperAffineInputPrice.data,GeneralPaperRayAffineScoreInput.fields_length]
  have hOld := GeneralPaperSourceEndpointLayerStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  refine ⟨GeneralPaperSourceAffineLayerRates.reservation model W m k,
    GeneralPaperSourceParametricCallerRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  obtain ⟨c,hScan,hLo,hHi,_⟩ := GeneralPaperSourceRayQueryStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex j hj state inv
  have hHeight := GeneralPaperRayUniformSize.static_time hm (Nat.mul_pos hN hD) hD prep.dictionary.label
    (GeneralPaperRayQueryWork.scores inputs.matrix) prep.threshold _ x w hx hw hBeta c hScan
  have hScan' : (GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c :=
    (GeneralPaperStaticScanPrice.data model.rat W prep.dictionary.label x w).trans hScan
  let loop := GeneralPaperParametricRunStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
    ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) fields 0 c.time
  have hZero := GeneralPaperEndpointPriceFacts.zero_height (inputs.controls.N*state.determinant.natAbs)
    state.determinant.natAbs m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs
  have hRun := GeneralPaperParametricRunStorage.native_bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD hED inputs.matrix x w hx hw
    (prepare m k).S prep.threshold _ hBeta hThreshold fields hLength.le hFields 0 c.time (by norm_num) hLo hHi hZero hHeight
    hW hK hM hIndex hBatch
  change loop≤GeneralPaperParametricRunStorage.profile W m (prepare m k).K (prepare m k).S R
    (GeneralPaperParametricRunStorage.price model W m (prepare m k).K (prepare m k).S R) at hRun
  have hWhole : loop≤GeneralPaperSourceParametricCallerRates.sourceProfile model W m k := by
    apply le_trans (b:=GeneralPaperSourceParametricCallerRates.profile model W m (prepare m k).K (prepare m k).S R)
    · unfold GeneralPaperSourceParametricCallerRates.profile
      exact hRun.trans (Nat.le_add_right _ _)
    · exact GeneralPaperSourceParametricCallerRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
  refine ⟨c,hScan',hWhole,?_⟩
  have hPair : ∀ n field (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K),n+1≤m →
      GeneralPaperRayAffineDPSize.FieldBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) field →
      GeneralPaperRayAffineDPSize.TableBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) n out.table →
      (∀ l,(field.read l).1≤(prepare m k).S) → 0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 →
      RationalHeight out.bracket.lower R → RationalHeight out.bracket.upper R →
      loop+GeneralPaperParametricStageCallerStorage.window model W inputs.matrix x w prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) field out.table out.bracket.lower out.bracket.upper≤
          GeneralPaperSourceParametricCallerRates.sourceProfile model W m k := by
    intro n field out hn hf hp _ hLo ho hHi hl hh
    have hStage := GeneralPaperParametricStageCallerStorage.native_bounded model W (inputs.controls.N*state.determinant.natAbs)
      state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs n (Nat.mul_pos hN hD) hD hED hn
      inputs.matrix x w hx hw prep.threshold _ hBeta hThreshold field out.table hf hp out.bracket.lower out.bracket.upper
      hLo ho hHi hl hh hW hK hM hIndex hBatch
    have hAtR : loop+GeneralPaperParametricStageCallerStorage.window model W inputs.matrix x w prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) field out.table out.bracket.lower out.bracket.upper≤
          GeneralPaperSourceParametricCallerRates.profile model W m (prepare m k).K (prepare m k).S R := Nat.add_le_add hRun hStage
    exact hAtR.trans (GeneralPaperSourceParametricCallerRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH)
  exact GeneralPaperRayGenerationCoverage.high_bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD inputs.matrix x w hx hw (prepare m k).S prep.threshold _ hScores
    (fun field out => loop+GeneralPaperParametricStageCallerStorage.window model W inputs.matrix x w prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) field out.table out.bracket.lower out.bracket.upper≤
        GeneralPaperSourceParametricCallerRates.sourceProfile model W m k) (fun _ => True) hPair (by intros; trivial)
    0 c.time (by norm_num) hLo hHi hZero hHeight

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      StageAtBound model W k (GeneralPaperSourceParametricCallerRates.reservation model W m k) prep inputs state hj := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hStart := GeneralPaperSourceBasisInputValidity.actual_start k Qv hm hQv weights hp hs b hb reciprocal
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperBasisControllerSound.stages_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    prep.dictionary v (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S prep.threshold inputs.controls.N hN
    (GeneralPaperScoreScaleParameters.score_cap m k) inputs.betaN inputs.initialGrid hStart j (Nat.le_of_lt hj)
  have hReturn : GeneralPaperBasisController.stages prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)=some state := by rw [GeneralPaperSharedBasisInputs.matrix_eq]; exact hr
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch j hj state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceEndpointCallerStorage
