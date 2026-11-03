import Blotto.GeneralPaperRayGenerationCoverage

/-! Actual reached-source generation/refinement storage. Native matrix and
packed ray owners remain retained; the current affine field/table also stay
owned throughout nested refinement/query phases. All source, score, table,
bracket, root and query premises are derived internally. -/
namespace Blotto.GeneralPaperSourceEndpointGenerationStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def PairAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (field : GeneralPaperRayAffineScoreStep.Field (prepare m k).K) (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  (∀ c,owner+GeneralPaperCrossingGenerationStorage.window model W field out.table c≤limit) ∧
    ∀ phase : ∀ t,GeneralPaperRayQueryStorage.Phase model W inputs.matrix x w t (prepare m k).S,
      ∀ p : GeneralPaperCrossingRefinementStorage.Phase,
        GeneralPaperAffineWitnessStorage.tableFoot W out.table+GeneralPaperAffineWitnessStorage.fieldFoot W field+
          (owner+GeneralPaperCrossingRefinementStorage.window model W
            (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
            (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
              ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)) out.bracket.lower out.bracket.upper
            (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1 p)≤limit

def BudgetAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  (∀ copied active,owner+GeneralPaperBudgetGenerationStorage.window model W copied out.table prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) active≤limit) ∧
    ∀ phase : ∀ t,GeneralPaperRayQueryStorage.Phase model W inputs.matrix x w t (prepare m k).S,
      ∀ p : GeneralPaperCrossingRefinementStorage.Phase,
        GeneralPaperAffineWitnessStorage.tableFoot W out.table+
          (owner+GeneralPaperCrossingRefinementStorage.window model W
            (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
            (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
              ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)) out.bracket.lower out.bracket.upper
            (GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1 p)≤limit

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ∃ c,(GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c ∧
    GeneralPaperRayGenerationCoverage.high model W inputs.matrix x w (prepare m k).S prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) 0 c.time
      (PairAtBound model W k limit prep inputs state hj) (BudgetAtBound model W k limit prep inputs state hj)

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  obtain ⟨c,hScan,hCoverage⟩ := h
  refine ⟨c,hScan,?_⟩
  apply GeneralPaperRayGenerationCoverage.high_mono model W inputs.matrix x w (prepare m k).S prep.threshold
    ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) _ _ _ _ ?_ ?_ 0 c.time hCoverage
  · intro field out hPair
    exact ⟨fun cursor => (hPair.1 cursor).trans hBC,fun phase p => (hPair.2 phase p).trans hBC⟩
  · intro out hBudget
    exact ⟨fun copied active => (hBudget.1 copied active).trans hBC,fun phase p => (hBudget.2 phase p).trans hBC⟩

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
      StageAtBound model W k (GeneralPaperSourceCrossingStreamRates.reservation model W m k) prep inputs state hj := by
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
  have hReady := GeneralPaperSourceRefinementStorageContext.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  have hOwners := GeneralPaperSourceRayQueryOwners.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim j hj state inv
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hD := Int.natAbs_pos.mpr inv.nonzero
  have hx := GeneralPaperRayAnchorBound.point k prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N hN
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv
  have hw := GeneralPaperRayAnchorBound.direction k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv (next hj) rfl
  have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
  have hCache := (GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_of_lt hj) state inv).1
  have hAux : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hRoot := GeneralPaperSourceRayStorageWidth.root_bound m k j b hb reciprocal state.determinant.natAbs inputs.betaN.natAbs (Nat.le_of_lt hj) hCache hAux
  change R≤GeneralPaperSourceRayStorageWidth.rootWidth m k at hRoot
  have hRH : R≤H := by dsimp only [H]; unfold GeneralPaperSourceRayStorageWidth.width; omega
  have hOuter : owner≤GeneralPaperSourceCrossingOperandStorageRates.reservation model W m k :=
    hOwners.trans (by
      unfold GeneralPaperSourceCrossingOperandStorageRates.reservation
        GeneralPaperSourceCrossingRefinementRates.reservation GeneralPaperSourceEndpointOwnerStorage.profile
      omega)
  have hRefLimit : GeneralPaperSourceCrossingOperandStorageRates.sourceProfile model W m k+
      GeneralPaperSourceCrossingRefinementRates.reservation model W m k≤GeneralPaperSourceCrossingStreamRates.reservation model W m k := by
    unfold GeneralPaperSourceCrossingStreamRates.reservation GeneralPaperSourceCrossingOperandStorageRates.reservation
    omega
  have hThreshold : prep.threshold≤(prepare m k).S := GeneralPaperTransferPreparation.threshold_le _ _ _ _ _ _ _ _
  have hScores : ∀ a l,((inputs.matrix.read a).read l).1≤(prepare m k).S := by
    intro a l
    rw [GeneralPaperSharedBasisInputs.matrix_eq]
    erw [GeneralPaperScoreMatrixWork.matrix_data (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)]
    simp only [FixedArrayTable.read_ofFn]
    convert GeneralPaperEncodedScoreMatrixStorage.score_bound v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) a l using 1
    rfl
  have hPair : ∀ n field (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K),n+1≤m →
      GeneralPaperRayAffineDPSize.FieldBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) field →
      GeneralPaperRayAffineDPSize.TableBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) n out.table →
      (∀ l,(field.read l).1≤(prepare m k).S) → 0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 →
      RationalHeight out.bracket.lower R → RationalHeight out.bracket.upper R →
      PairAtBound model W k (GeneralPaperSourceCrossingStreamRates.reservation model W m k) prep inputs state hj field out := by
    intro n field out hn hf hp hScore hLo ho hHi hl hh
    have hTable := GeneralPaperAffineWitnessStorage.table_bound W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) n m inputs.betaN.natAbs (Nat.mul_pos hN hD) hD (by omega) out.table hp
    have hField := GeneralPaperAffineWitnessStorage.field_bound W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) m inputs.betaN.natAbs (prepare m k).S (Nat.mul_pos hN hD) hD (by omega) field hf hScore
    have hAffine : GeneralPaperAffineWitnessStorage.tableFoot W out.table+GeneralPaperAffineWitnessStorage.fieldFoot W field≤
        GeneralPaperSourceCrossingOperandStorageRates.sourceProfile model W m k := by
      apply le_trans (b:=GeneralPaperSourceCrossingOperandStorageRates.profile model W m (prepare m k).K (prepare m k).S R)
      · change GeneralPaperAffineWitnessStorage.tableFoot W out.table≤GeneralPaperAffineWitnessStorage.tableProfile W (prepare m k).S (prepare m k).K m R at hTable
        change GeneralPaperAffineWitnessStorage.fieldFoot W field≤GeneralPaperAffineWitnessStorage.fieldProfile W (prepare m k).K (prepare m k).S R at hField
        unfold GeneralPaperSourceCrossingOperandStorageRates.profile
        omega
      · exact GeneralPaperSourceCrossingOperandStorageRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
    constructor
    · intro c
      have hGen := GeneralPaperCrossingGenerationStorage.bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
        m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs n (Nat.mul_pos hN hD) hD hn field out.table hf hp hScore c
      have hWhole : GeneralPaperCrossingGenerationStorage.window model W field out.table c≤GeneralPaperSourceCrossingStreamRates.sourceProfile model W m k :=
        hGen.trans ((show GeneralPaperCrossingGenerationStorage.profile model W m (prepare m k).K (prepare m k).S R≤
            GeneralPaperSourceCrossingStreamRates.profile model W m (prepare m k).K (prepare m k).S R by unfold GeneralPaperSourceCrossingStreamRates.profile; omega).trans
          (GeneralPaperSourceCrossingStreamRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH))
      exact Nat.add_le_add hOuter hWhole
    · intro phase p
      have hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1.length≤((prepare m k).S+1)*((prepare m k).K*(prepare m k).K) := by
        rw [GeneralPaperNativeAffinePrices.crossings_data]
        exact GeneralPaperRayAffineScoreStep.crossings_length field out.table
      have hHeights : ∀ t∈(GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1,RationalHeight t R := by
        intro t ht
        rw [GeneralPaperNativeAffinePrices.crossings_data] at ht
        exact GeneralPaperRayUniformSize.stage_roots (Nat.mul_pos hN hD) hD hn field out.table hf hp t ht
      have hRef := hReady out.bracket.lower out.bracket.upper _ hLo ho hHi hl hh hLen hHeights phase p
      simpa only [Nat.add_assoc] using (Nat.add_le_add hAffine hRef).trans hRefLimit
  have hBudget : ∀ out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K,
      GeneralPaperRayAffineDPSize.TableBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) m out.table →
      0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 → RationalHeight out.bracket.lower R → RationalHeight out.bracket.upper R →
      BudgetAtBound model W k (GeneralPaperSourceCrossingStreamRates.reservation model W m k) prep inputs state hj out := by
    intro out hp hLo ho hHi hl hh
    have hTable := GeneralPaperAffineWitnessStorage.table_bound W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) m m inputs.betaN.natAbs (Nat.mul_pos hN hD) hD le_rfl out.table hp
    have hAffine : GeneralPaperAffineWitnessStorage.tableFoot W out.table≤GeneralPaperSourceCrossingOperandStorageRates.sourceProfile model W m k := by
      apply le_trans (b:=GeneralPaperSourceCrossingOperandStorageRates.profile model W m (prepare m k).K (prepare m k).S R)
      · change GeneralPaperAffineWitnessStorage.tableFoot W out.table≤GeneralPaperAffineWitnessStorage.tableProfile W (prepare m k).S (prepare m k).K m R at hTable
        unfold GeneralPaperSourceCrossingOperandStorageRates.profile
        omega
      · exact GeneralPaperSourceCrossingOperandStorageRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
    constructor
    · intro copied active
      have hGen := GeneralPaperBudgetGenerationStorage.bounded model W copied (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
        m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs m (Nat.mul_pos hN hD) hD le_rfl out.table hp prep.threshold hThreshold _ hBeta active
      have hWhole : GeneralPaperBudgetGenerationStorage.window model W copied out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) active≤
          GeneralPaperSourceCrossingStreamRates.sourceProfile model W m k :=
        hGen.trans ((show GeneralPaperBudgetGenerationStorage.profile model W m (prepare m k).K (prepare m k).S R≤
            GeneralPaperSourceCrossingStreamRates.profile model W m (prepare m k).K (prepare m k).S R by unfold GeneralPaperSourceCrossingStreamRates.profile; omega).trans
          (GeneralPaperSourceCrossingStreamRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH))
      exact Nat.add_le_add hOuter hWhole
    · intro phase p
      have hKPositive := GeneralPaperScoreScaleParameters.labels_positive m k
      have hLen : (GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1.length≤
          ((prepare m k).S+1)*((prepare m k).K*(prepare m k).K) := by
        rw [GeneralPaperBudgetCrossingPrice.data]
        exact (GeneralPaperRayBudgetCrossings.batch_length _ _ _).trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos hKPositive hKPositive))
      have hHeights : ∀ t∈(GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1,RationalHeight t R := by
        intro t ht
        rw [GeneralPaperBudgetCrossingPrice.data] at ht
        exact GeneralPaperRayUniformSize.budget_roots (Nat.mul_pos hN hD) hD le_rfl out.table hp prep.threshold _ hBeta t ht
      have hRef := hReady out.bracket.lower out.bracket.upper _ hLo ho hHi hl hh hLen hHeights phase p
      exact (Nat.add_le_add hAffine hRef).trans hRefLimit
  obtain ⟨c,hScan,hLo,hHi,_⟩ := GeneralPaperSourceRayQueryStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex j hj state inv
  have hHeight := GeneralPaperRayUniformSize.static_time hm (Nat.mul_pos hN hD) hD prep.dictionary.label
    (GeneralPaperRayQueryWork.scores inputs.matrix) prep.threshold _ x w hx hw hBeta c hScan
  have hScan' : (GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c :=
    (GeneralPaperStaticScanPrice.data model.rat W prep.dictionary.label x w).trans hScan
  refine ⟨c,hScan',?_⟩
  exact GeneralPaperRayGenerationCoverage.high_bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
    1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD inputs.matrix x w hx hw (prepare m k).S prep.threshold _ hScores
    (PairAtBound model W k (GeneralPaperSourceCrossingStreamRates.reservation model W m k) prep inputs state hj)
    (BudgetAtBound model W k (GeneralPaperSourceCrossingStreamRates.reservation model W m k) prep inputs state hj) hPair hBudget
    0 c.time (by norm_num) hLo hHi (GeneralPaperEndpointPriceFacts.zero_height _ _ _ _ _ _) hHeight

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
      StageAtBound model W k (GeneralPaperSourceCrossingStreamRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceEndpointGenerationStorage
