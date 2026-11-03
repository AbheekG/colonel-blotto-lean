import Blotto.GeneralPaperSourceBlockerRecoveryRates

/-! Actual reached-source final-budget return and blocker recovery. Full
input/affine/matrix/packed-ray owners and returned final-refinement buffers
remain retained while the literal successful bracket is decoded. Native
return equations derive every table, root, label and price premise. -/
namespace Blotto.GeneralPaperSourceFinalRecoveryStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperSourceEndpointInputStorage (resident)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 8192

def BudgetAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  let points := (GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1
  let base := resident W k inputs state hj+(GeneralPaperAffineWitnessStorage.tableFoot W out.table+
    (owner+GeneralPaperCrossingRefinementStorage.window model W
      (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
      (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t .minimum) out.bracket.lower out.bracket.upper points .returned))
  let final := GeneralPaperFinalRefinementReturnStorage.window model W inputs.matrix out.table x w prep.threshold
    ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) out.bracket.lower out.bracket.upper
  base+final≤limit ∧ ∀ b,(GeneralPaperFinalRefinementPrice.bits model W inputs.matrix out.table x w prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) out.bracket.lower out.bracket.upper).1=some b →
    ∀ copied active,base+(final+GeneralPaperHighBlockerStorage.window model W m copied out.table prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) b.lower b.upper active)≤limit

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ∃ previousReserve recoveryReserve,
    GeneralPaperSourceStaticConstructionStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      (∃ c,(GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c ∧
        GeneralPaperRayGenerationCoverage.high model W inputs.matrix x w (prepare m k).S prep.threshold
          ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) 0 c.time (fun _ _ => True)
          (BudgetAtBound model W k (previousReserve+recoveryReserve) prep inputs state hj)) ∧
      previousReserve+recoveryReserve≤limit

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  obtain ⟨D,F,hPrevious,hRecovery,hSum⟩ := h
  exact ⟨D,F,hPrevious,hRecovery,hSum.trans hBC⟩

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
    ∀ j (hj : j<m*((prepare m k).K-1)) (state : State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state →
      StageAtBound model W k (GeneralPaperSourceBlockerRecoveryRates.reservation model W m k) prep inputs state hj := by
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
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
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
  have hH : 1≤H := by dsimp only [H]; unfold GeneralPaperSourceRayStorageWidth.width; omega
  have hxH : ∀ a,RationalHeight (x a) H := fun a =>
    (GeneralPaperRayOperandStorageHeight.point (E:=state.determinant.natAbs) (m:=m)
      (V:=j*(prepare m k).H*(m+1)+1) (P:=inputs.betaN.natAbs) (Nat.mul_pos hN hD) (hx a)).mono hRH
  have hwH : ∀ a,RationalHeight (w a) H := fun a =>
    (GeneralPaperRayOperandStorageHeight.direction (D:=inputs.controls.N*state.determinant.natAbs) (m:=m)
      (X:=1) (P:=inputs.betaN.natAbs) hD (hw a)).mono hRH
  have hResident : resident W k inputs state hj≤GeneralPaperSourceAffineInputRates.sourceProfile W m k :=
    (GeneralPaperAffineInputStorage.fields_bound W (prepare m k).S H hH inputs.matrix hScores x w hxH hwH).trans
      (GeneralPaperSourceAffineInputRates.list_le_profile W m (prepare m k).K (prepare m k).S H)
  have hED : state.determinant.natAbs∣inputs.controls.N*state.determinant.natAbs := ⟨inputs.controls.N,Nat.mul_comm _ _⟩
  have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  have hReady := GeneralPaperSourceRefinementStorageContext.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  have hOld := GeneralPaperSourceStaticConstructionStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  refine ⟨GeneralPaperSourceStaticConstructionRates.reservation model W m k,
    GeneralPaperSourceBlockerRecoveryRates.sourceProfile model W m k,hOld,?_,le_rfl⟩
  have hBudget : ∀ out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K,
      GeneralPaperRayAffineDPSize.TableBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) m out.table →
      0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 → RationalHeight out.bracket.lower R → RationalHeight out.bracket.upper R →
      BudgetAtBound model W k (GeneralPaperSourceStaticConstructionRates.reservation model W m k+
        GeneralPaperSourceBlockerRecoveryRates.sourceProfile model W m k) prep inputs state hj out := by
    intro out hp hLo ho hHi hl hh
    have hTable := GeneralPaperAffineWitnessStorage.table_bound W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) m m inputs.betaN.natAbs (Nat.mul_pos hN hD) hD le_rfl out.table hp
    have hAffine : GeneralPaperAffineWitnessStorage.tableFoot W out.table≤GeneralPaperSourceCrossingOperandStorageRates.sourceProfile model W m k := by
      apply le_trans (b:=GeneralPaperSourceCrossingOperandStorageRates.profile model W m (prepare m k).K (prepare m k).S R)
      · change GeneralPaperAffineWitnessStorage.tableFoot W out.table≤GeneralPaperAffineWitnessStorage.tableProfile W (prepare m k).S (prepare m k).K m R at hTable
        unfold GeneralPaperSourceCrossingOperandStorageRates.profile
        omega
      · exact GeneralPaperSourceCrossingOperandStorageRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
    have hKPositive := GeneralPaperScoreScaleParameters.labels_positive m k
    have hLen : (GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1.length≤
        ((prepare m k).S+1)*((prepare m k).K*(prepare m k).K) := by
      rw [GeneralPaperBudgetCrossingPrice.data]
      exact (GeneralPaperRayBudgetCrossings.batch_length _ _ _).trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos hKPositive hKPositive))
    have hHeights : ∀ t∈(GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1,RationalHeight t R := by
      intro t ht
      rw [GeneralPaperBudgetCrossingPrice.data] at ht
      exact GeneralPaperRayUniformSize.budget_roots (Nat.mul_pos hN hD) hD le_rfl out.table hp prep.threshold _ hBeta t ht
    have hRef := hReady out.bracket.lower out.bracket.upper _ hLo ho hHi hl hh hLen hHeights (fun _ => .minimum) .returned
    have hBaseCap : GeneralPaperSourceAffineInputRates.sourceProfile W m k+
        (GeneralPaperSourceCrossingOperandStorageRates.sourceProfile model W m k+
          GeneralPaperSourceCrossingRefinementRates.reservation model W m k)≤GeneralPaperSourceStaticConstructionRates.reservation model W m k := by
      unfold GeneralPaperSourceStaticConstructionRates.reservation GeneralPaperSourceStaticScanRates.reservation
        GeneralPaperSourceStaticRowRates.reservation GeneralPaperSourceParametricCallerRates.reservation GeneralPaperSourceAffineLayerRates.reservation
        GeneralPaperSourceAffineInputRates.reservation GeneralPaperSourceCrossingStreamRates.reservation GeneralPaperSourceCrossingOperandStorageRates.reservation
      omega
    have hBase := (Nat.add_le_add hResident (Nat.add_le_add hAffine hRef)).trans hBaseCap
    have hFinal := GeneralPaperFinalRefinementReturnStorage.bounded model W (inputs.controls.N*state.determinant.natAbs)
      state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD hED inputs.matrix out.table hp
      x w hx hw prep.threshold hThreshold _ hBeta out.bracket.lower out.bracket.upper hLo ho hHi hl hh hW hK hM hIndex hFinalIndex
    constructor
    · have hWhole : GeneralPaperFinalRefinementReturnStorage.window model W inputs.matrix out.table x w prep.threshold
          ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) out.bracket.lower out.bracket.upper≤GeneralPaperSourceBlockerRecoveryRates.sourceProfile model W m k := by
        apply hFinal.trans
        apply le_trans (b:=GeneralPaperSourceBlockerRecoveryRates.profile model W m (prepare m k).K (prepare m k).S R)
        · change GeneralPaperFinalRefinementReturnStorage.profile model W m (prepare m k).K (prepare m k).S R≤_
          unfold GeneralPaperSourceBlockerRecoveryRates.profile
          omega
        · exact GeneralPaperSourceBlockerRecoveryRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
      exact Nat.add_le_add hBase hWhole
    · intro b hReturn copied active
      have hNative : GeneralPaperRayFinalBudget.finish inputs.matrix out.table x w prep.threshold
          ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) out.bracket.lower out.bracket.upper=some b :=
        (GeneralPaperFinalRefinementPrice.bits_data model W inputs.matrix out.table x w prep.threshold _ out.bracket.lower out.bracket.upper).symm.trans hReturn
      have hBounds := GeneralPaperRayParametricRunSize.finish (Nat.mul_pos hN hD) hD (Nat.le_refl m)
        (GeneralPaperRayPricedPredicate.query inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
        out.table hp prep.threshold _ out.bracket.lower out.bracket.upper hBeta hl hh b hNative
      have hRecover := GeneralPaperHighBlockerStorage.bounded model W copied (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
        m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD out.table hp prep.threshold hThreshold _ hBeta
        b.lower b.upper hBounds.1 hBounds.2.1 hW hM active
      have hWhole : GeneralPaperFinalRefinementReturnStorage.window model W inputs.matrix out.table x w prep.threshold
          ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) out.bracket.lower out.bracket.upper+
          GeneralPaperHighBlockerStorage.window model W m copied out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) b.lower b.upper active≤
            GeneralPaperSourceBlockerRecoveryRates.sourceProfile model W m k := by
        apply (Nat.add_le_add hFinal hRecover).trans
        apply le_trans (b:=GeneralPaperSourceBlockerRecoveryRates.profile model W m (prepare m k).K (prepare m k).S R)
        · change GeneralPaperFinalRefinementReturnStorage.profile model W m (prepare m k).K (prepare m k).S R+
            GeneralPaperHighBlockerStorage.profile model W m (prepare m k).K (prepare m k).S R≤_
          unfold GeneralPaperSourceBlockerRecoveryRates.profile
          omega
        · exact GeneralPaperSourceBlockerRecoveryRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
      exact Nat.add_le_add hBase hWhole
  obtain ⟨c,hScan,hLo,hHi,_⟩ := GeneralPaperSourceRayQueryStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex j hj state inv
  have hHeight := GeneralPaperRayUniformSize.static_time hm (Nat.mul_pos hN hD) hD prep.dictionary.label
    (GeneralPaperRayQueryWork.scores inputs.matrix) prep.threshold _ x w hx hw hBeta c hScan
  have hScan' : (GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c :=
    (GeneralPaperStaticScanPrice.data model.rat W prep.dictionary.label x w).trans hScan
  refine ⟨c,hScan',?_⟩
  exact GeneralPaperRayGenerationCoverage.high_bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD inputs.matrix x w hx hw (prepare m k).S prep.threshold _ hScores
    (fun _ _ => True) (BudgetAtBound model W k (GeneralPaperSourceStaticConstructionRates.reservation model W m k+
      GeneralPaperSourceBlockerRecoveryRates.sourceProfile model W m k) prep inputs state hj) (by intros; trivial) hBudget
    0 c.time (by norm_num) hLo hHi (GeneralPaperEndpointPriceFacts.zero_height _ _ _ _ _ _) hHeight

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W)
    (j : ℕ) (hj : j<m*((prepare m k).K-1)) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
      StageAtBound model W k (GeneralPaperSourceBlockerRecoveryRates.reservation model W m k) prep inputs state hj := by
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
  refine ⟨state,?_,source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch hFinalIndex j hj state inv⟩
  exact (GeneralPaperBasisControllerBits.stages_data model W _ _ _ _ _ _ _ _ _).trans hReturn

end Blotto.GeneralPaperSourceFinalRecoveryStorage
