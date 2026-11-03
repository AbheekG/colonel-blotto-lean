import Blotto.GeneralPaperSourceAffineInputRates

/-! The full native affine-input list remains owned throughout every
actual parametric crossing generation/refinement call. Native input
construction is also covered. Actual reached source states derive all
anchor/score bounds; no additional run-time observer or oracle is added. -/
namespace Blotto.GeneralPaperSourceEndpointInputStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def resident {T m j : ℕ} (W k : ℕ)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : ℕ :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  GeneralPaperAffineInputStorage.fieldsFoot W (GeneralPaperAffineInputPrice.run (fun w => w) W inputs.matrix x w).1

def ConstructionAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ∀ outer (ho : outer≤m) (a : Fin m) inner (hi : inner≤(prepare m k).K) (l : Fin (prepare m k).K) copied,
    GeneralPaperSourceRayQueryOwners.window model W k inputs state hj+
      GeneralPaperAffineInputStorage.window W inputs.matrix x w outer ho a inner hi l copied≤limit

def PairAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (field : GeneralPaperRayAffineScoreStep.Field (prepare m k).K) (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let resident := resident W k inputs state hj
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  (∀ c,resident+(owner+GeneralPaperCrossingGenerationStorage.window model W field out.table c)≤limit) ∧
    ∀ phase : ∀ t,GeneralPaperRayQueryStorage.Phase model W inputs.matrix x w t (prepare m k).S,
      ∀ p : GeneralPaperCrossingRefinementStorage.Phase,
        resident+(GeneralPaperAffineWitnessStorage.tableFoot W out.table+GeneralPaperAffineWitnessStorage.fieldFoot W field+
          (owner+GeneralPaperCrossingRefinementStorage.window model W
            (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
            (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
              ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)) out.bracket.lower out.bracket.upper
            (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field out.table).1 p))≤limit

def BudgetAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1))
    (out : GeneralPaperRayParametricDP.Output (prepare m k).S (prepare m k).K) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let resident := resident W k inputs state hj
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  (∀ copied active,resident+(owner+GeneralPaperBudgetGenerationStorage.window model W copied out.table prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) active)≤limit) ∧
    ∀ phase : ∀ t,GeneralPaperRayQueryStorage.Phase model W inputs.matrix x w t (prepare m k).S,
      ∀ p : GeneralPaperCrossingRefinementStorage.Phase,
        resident+(GeneralPaperAffineWitnessStorage.tableFoot W out.table+
          (owner+GeneralPaperCrossingRefinementStorage.window model W
            (GeneralPaperRayPredicateBits.run model W inputs.matrix x w (prepare m k).S prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)))
            (fun t => owner+GeneralPaperRayPredicateStorage.window model W inputs.matrix x w (prepare m k).S prep.threshold
              ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) t (phase t)) out.bracket.lower out.bracket.upper
            (GeneralPaperBudgetCrossingPrice.run model.rat W out.table prep.threshold ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ))).1 p))≤limit

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  ConstructionAtBound model W k limit inputs state hj ∧
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
  rcases h with ⟨hInput,hStage⟩
  refine ⟨fun outer ho a inner hi l copied => (hInput outer ho a inner hi l copied).trans hBC,?_⟩
  obtain ⟨c,hScan,hCoverage⟩ := hStage
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
      StageAtBound model W k (GeneralPaperSourceAffineInputRates.reservation model W m k) prep inputs state hj := by
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
  have hOld := GeneralPaperSourceEndpointGenerationStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  refine ⟨?_,?_⟩
  · intro outer ho a inner hi l copied
    have hInput := GeneralPaperAffineInputStorage.bounded W (prepare m k).S H hH inputs.matrix hScores x w hxH hwH
      hW hK hM outer ho a inner hi l copied
    exact Nat.add_le_add hOuter hInput
  · obtain ⟨c,hScan,hCoverage⟩ := hOld
    refine ⟨c,hScan,?_⟩
    apply GeneralPaperRayGenerationCoverage.high_mono model W inputs.matrix x w (prepare m k).S prep.threshold
      ((inputs.betaN:ℚ)/(inputs.controls.N:ℚ)) _ _ _ _ ?_ ?_ 0 c.time hCoverage
    · intro field out hPair
      exact ⟨fun cursor => (Nat.add_le_add hResident (hPair.1 cursor)).trans_eq (Nat.add_comm _ _),
        fun phase p => (Nat.add_le_add hResident (hPair.2 phase p)).trans_eq (Nat.add_comm _ _)⟩
    · intro out hBudget
      exact ⟨fun copied active => (Nat.add_le_add hResident (hBudget.1 copied active)).trans_eq (Nat.add_comm _ _),
        fun phase p => (Nat.add_le_add hResident (hBudget.2 phase p)).trans_eq (Nat.add_comm _ _)⟩

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
      StageAtBound model W k (GeneralPaperSourceAffineInputRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceEndpointInputStorage
