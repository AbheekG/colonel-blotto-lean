import Blotto.GeneralPaperSourceAffineLayerRates

/-! Actual reached-source affine initialization and layer construction.
The whole input list, affine field/table, matrix/packed ray owners and all
returned-refinement buffers stay retained through midpoint/step windows.
The midpoint is the literal result of each actual successful refinement. -/
namespace Blotto.GeneralPaperSourceEndpointLayerStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperSourceEndpointInputStorage (resident)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def InitialAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  ∀ count (hc : count≤(prepare m k).S+1) (s : Fin ((prepare m k).S+1)),
    resident W k inputs state hj+GeneralPaperSourceRayQueryOwners.window model W k inputs state hj+
      GeneralPaperAffineInitialStorage.window W (prepare m k).S (prepare m k).K count hc s≤limit

def LayerAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (field : GeneralPaperRayAffineScoreStep.Field (prepare m k).K)
    (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  let points := (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1
  let query := GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))
  ∀ b,(GeneralPaperRayBitRefinement.run model W inputs.matrix x w (prepare m k).S prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) out.bracket.lower out.bracket.upper points).bracket=some b →
    ∀ copied count (hc : count≤(prepare m k).S+1) (s : Fin ((prepare m k).S+1)) active,
      (resident W k inputs state hj+GeneralPaperAffineWitnessStorage.tableFoot W out.table+
        GeneralPaperAffineWitnessStorage.fieldFoot W field+
        (owner+GeneralPaperCrossingRefinementStorage.window model W query
          (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
            ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t .minimum) out.bracket.lower out.bracket.upper points .returned))+
        (GeneralPaperRayMidpointStorage.window model W b.lower b.upper+
          GeneralPaperAffineStepStorage.window model W copied (GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper).1
            field out.table count hc s active)≤limit

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  GeneralPaperSourceEndpointInputStorage.StageAtBound model W k limit prep inputs state hj ∧
    InitialAtBound model W k limit inputs state hj ∧
    ∃ c,(GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c ∧
      GeneralPaperRayGenerationCoverage.high model W inputs.matrix x w (prepare m k).S prep.threshold
        ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) 0 c.time (LayerAtBound model W k limit prep inputs state hj) (fun _ => True)

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  rcases h with ⟨hOld,hInitial,c,hScan,hCoverage⟩
  refine ⟨GeneralPaperSourceEndpointInputStorage.stage_mono model W k prep inputs state hj B C hBC hOld,
    fun count hc s => (hInitial count hc s).trans hBC,c,hScan,?_⟩
  apply GeneralPaperRayGenerationCoverage.high_mono model W inputs.matrix x w (prepare m k).S prep.threshold
    ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) _ _ _ _ ?_ (fun _ _ => trivial) 0 c.time hCoverage
  intro field out hLayer b hb copied count hc s active
  exact (hLayer b hb copied count hc s active).trans hBC

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
      StageAtBound model W k (GeneralPaperSourceAffineLayerRates.reservation model W m k) prep inputs state hj := by
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
  have hOwners := GeneralPaperSourceRayQueryOwners.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim j hj state inv
  have hOuter : owner≤GeneralPaperSourceCrossingStreamRates.reservation model W m k :=
    hOwners.trans (by
      unfold GeneralPaperSourceCrossingStreamRates.reservation GeneralPaperSourceCrossingOperandStorageRates.reservation
        GeneralPaperSourceCrossingRefinementRates.reservation GeneralPaperSourceEndpointOwnerStorage.profile
      omega)
  have hReady := GeneralPaperSourceRefinementStorageContext.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  have hOld := GeneralPaperSourceEndpointInputStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  have hOldLimit : GeneralPaperSourceAffineInputRates.reservation model W m k≤GeneralPaperSourceAffineLayerRates.reservation model W m k := by
    unfold GeneralPaperSourceAffineLayerRates.reservation; omega
  have hRetained : resident W k inputs state hj+owner≤GeneralPaperSourceAffineInputRates.reservation model W m k := by
    simpa only [GeneralPaperSourceAffineInputRates.reservation,Nat.add_comm] using Nat.add_le_add hResident hOuter
  refine ⟨GeneralPaperSourceEndpointInputStorage.stage_mono model W k prep inputs state hj _ _ hOldLimit hOld,?_,?_⟩
  · intro count hc s
    have hInitial := GeneralPaperAffineInitialStorage.bounded W (prepare m k).S (prepare m k).K hW hIndex count hc s
    have hProfile : GeneralPaperAffineInitialStorage.profile W (prepare m k).S (prepare m k).K≤
        GeneralPaperSourceAffineLayerRates.sourceProfile model W m k := by
      unfold GeneralPaperSourceAffineLayerRates.sourceProfile GeneralPaperSourceAffineLayerRates.profile
      omega
    exact Nat.add_le_add hRetained (hInitial.trans hProfile)
  · have hPair : ∀ n field (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K),n+1≤m →
        GeneralPaperRayAffineDPSize.FieldBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) field →
        GeneralPaperRayAffineDPSize.TableBounded (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs 1 (j*(prepare m k).H*(m+1)+1) n out.table →
        (∀ l,(field.read l).1≤(prepare m k).S) → 0≤out.bracket.lower → out.bracket.lower≤out.bracket.upper → out.bracket.upper≤1 →
        RationalHeight out.bracket.lower R → RationalHeight out.bracket.upper R →
        LayerAtBound model W k (GeneralPaperSourceAffineLayerRates.reservation model W m k) prep inputs state hj field out := by
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
      have hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1.length≤((prepare m k).S+1)*((prepare m k).K*(prepare m k).K) := by
        rw [GeneralPaperNativeAffinePrices.crossings_data]
        exact GeneralPaperRayAffineScoreStep.crossings_length field out.table
      have hHeights : ∀ t∈(GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1,RationalHeight t R := by
        intro t ht
        rw [GeneralPaperNativeAffinePrices.crossings_data] at ht
        exact GeneralPaperRayUniformSize.stage_roots (Nat.mul_pos hN hD) hD hn field out.table hf hp t ht
      have hRef := hReady out.bracket.lower out.bracket.upper _ hLo ho hHi hl hh hLen hHeights (fun _ => .minimum) .returned
      have hBaseCap : GeneralPaperSourceAffineInputRates.sourceProfile W m k+
          (GeneralPaperSourceCrossingOperandStorageRates.sourceProfile model W m k+
            GeneralPaperSourceCrossingRefinementRates.reservation model W m k)≤GeneralPaperSourceAffineInputRates.reservation model W m k := by
        unfold GeneralPaperSourceAffineInputRates.reservation GeneralPaperSourceCrossingStreamRates.reservation
          GeneralPaperSourceCrossingOperandStorageRates.reservation
        omega
      have hBase := (Nat.add_le_add hResident (Nat.add_le_add hAffine hRef)).trans hBaseCap
      intro b hb copied count hc s active
      have hNative : GeneralPaperRayCrossingRefinement.narrow
          (GeneralPaperRayPricedPredicate.query inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
          out.bracket.lower out.bracket.upper (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1=some b :=
        (GeneralPaperRayBitRefinement.data model W inputs.matrix x w (prepare m k).S prep.threshold _ out.bracket.lower out.bracket.upper _).symm.trans hb
      have hBounds := GeneralPaperRayBracketSize.narrow_height _ out.bracket.lower out.bracket.upper _ R hl hh hHeights b hNative
      have hMidpoint := GeneralPaperRayMidpointStorage.bounded model W R b.lower b.upper hBounds.1 hBounds.2
      have hSample : RationalHeight (GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper).1 (2*R+3) :=
        GeneralPaperRayAffineBound.midpoint_height hBounds.1 hBounds.2
      have hStep := GeneralPaperAffineStepStorage.bounded model W copied (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
        m 1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs n (Nat.mul_pos hN hD) hD hn _ hSample
        field out.table hf hp hScore hW hIndex count hc s active
      have hLayer : GeneralPaperRayMidpointStorage.window model W b.lower b.upper+
          GeneralPaperAffineStepStorage.window model W copied (GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper).1
            field out.table count hc s active≤GeneralPaperSourceAffineLayerRates.sourceProfile model W m k := by
        apply (Nat.add_le_add hMidpoint hStep).trans
        apply le_trans (b:=GeneralPaperSourceAffineLayerRates.profile model W m (prepare m k).K (prepare m k).S R)
        · change GeneralPaperRayMidpointStorage.profile model W R+GeneralPaperAffineStepStorage.profile model W m (prepare m k).K (prepare m k).S R≤_
          unfold GeneralPaperSourceAffineLayerRates.profile
          omega
        · exact GeneralPaperSourceAffineLayerRates.height_mono model W m (prepare m k).K (prepare m k).S R H hRH
      change _≤GeneralPaperSourceAffineInputRates.reservation model W m k+
        GeneralPaperSourceAffineLayerRates.sourceProfile model W m k
      simpa only [Nat.add_assoc] using Nat.add_le_add hBase hLayer
    obtain ⟨c,hScan,hLo,hHi,_⟩ := GeneralPaperSourceRayQueryStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex j hj state inv
    have hBeta := GeneralPaperRayAnchorBound.budget inputs.controls.N hN state.determinant.natAbs inputs.betaN
    have hHeight := GeneralPaperRayUniformSize.static_time hm (Nat.mul_pos hN hD) hD prep.dictionary.label
      (GeneralPaperRayQueryWork.scores inputs.matrix) prep.threshold _ x w hx hw hBeta c hScan
    have hScan' : (GeneralPaperStaticScanPrice.run model.rat W prep.dictionary.label x w).choice=some c :=
      (GeneralPaperStaticScanPrice.data model.rat W prep.dictionary.label x w).trans hScan
    refine ⟨c,hScan',?_⟩
    exact GeneralPaperRayGenerationCoverage.high_bounded model W (inputs.controls.N*state.determinant.natAbs) state.determinant.natAbs
      1 (j*(prepare m k).H*(m+1)+1) inputs.betaN.natAbs (Nat.mul_pos hN hD) hD inputs.matrix x w hx hw (prepare m k).S prep.threshold _ hScores
      (LayerAtBound model W k (GeneralPaperSourceAffineLayerRates.reservation model W m k) prep inputs state hj)
      (fun _ => True) hPair (by intros; trivial) 0 c.time (by norm_num) hLo hHi (GeneralPaperEndpointPriceFacts.zero_height _ _ _ _ _ _) hHeight

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
      StageAtBound model W k (GeneralPaperSourceAffineLayerRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceEndpointLayerStorage
