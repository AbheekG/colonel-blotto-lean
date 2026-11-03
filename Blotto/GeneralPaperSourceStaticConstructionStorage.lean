import Blotto.GeneralPaperSourceStaticConstructionRates

/-! Complete reached-source static construction plus execution. The old
scan/data/caller reserve and new constructor reserve are summed; actual
index enumeration and current sparse-row construction coexist with the
full native scan reservation and original matrix/packed ray owners. -/
namespace Blotto.GeneralPaperSourceStaticConstructionStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def StageAtBound {T m j : ℕ} (model : RationalCostModel) (W k limit : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) : Prop :=
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  ∃ previousReserve constructorReserve,
    GeneralPaperSourceStaticScanStorage.StageAtBound model W k previousReserve prep inputs state hj ∧
      (∀ copied activeField activeLabel activeVariable activeBudget,
        owner+GeneralPaperStaticEnumerationStorage.window W T m (prepare m k).K copied activeField activeLabel activeVariable activeBudget≤
          previousReserve+constructorReserve) ∧
      (∀ copied activeField activeLabel activeVariable activeBudget (i : GeneralPaperStaticRayRows.StaticIndex T m (prepare m k).K),
        (owner+GeneralPaperNativeStaticScanStorage.window model W prep.dictionary.label x w (some i))+
          (GeneralPaperStaticEnumerationStorage.window W T m (prepare m k).K copied activeField activeLabel activeVariable activeBudget+
            GeneralPaperStaticRowConstructionStorage.window W copied prep.dictionary.label i)≤previousReserve+constructorReserve) ∧
      previousReserve+constructorReserve≤limit

theorem stage_mono {T m j : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State j (m*((prepare m k).K-1))) (hj : j<m*((prepare m k).K-1)) (B C : ℕ) (hBC : B≤C)
    (h : StageAtBound model W k B prep inputs state hj) : StageAtBound model W k C prep inputs state hj := by
  obtain ⟨D,F,hPrevious,hEnum,hRows,hSum⟩ := h
  exact ⟨D,F,hPrevious,hEnum,hRows,hSum.trans hBC⟩

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
      StageAtBound model W k (GeneralPaperSourceStaticConstructionRates.reservation model W m k) prep inputs state hj := by
  dsimp only
  intro j hj state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let x := reader (GeneralPaperBasisFreshPoint.run inputs.controls.N inputs.betaN state.determinant state.adjugate state.rows inputs.initialGrid).point
  let w := reader (GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows (next hj)).velocity
  let owner := GeneralPaperSourceRayQueryOwners.window model W k inputs state hj
  let T := (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows
  have hOld := GeneralPaperSourceStaticScanStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch j hj state inv
  obtain ⟨D,F,_hPrevious,hScans,hSum⟩ := hOld
  have hOwner : owner≤GeneralPaperSourceStaticScanRates.reservation model W m k :=
    (Nat.le_add_right owner (GeneralPaperNativeStaticScanStorage.window model W prep.dictionary.label x w none)).trans ((hScans none).trans hSum)
  refine ⟨GeneralPaperSourceStaticScanRates.reservation model W m k,
    GeneralPaperSourceStaticConstructionRates.sourceProfile model W m k,?_,?_,?_,le_rfl⟩
  · exact GeneralPaperSourceStaticScanStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal
      hW hK hM hIndex hDim hBatch j hj state inv
  · intro copied activeField activeLabel activeVariable activeBudget
    have hEnum := GeneralPaperStaticEnumerationStorage.bounded W T m (prepare m k).K copied activeField activeLabel activeVariable activeBudget
    have hWhole : GeneralPaperStaticEnumerationStorage.window W T m (prepare m k).K copied activeField activeLabel activeVariable activeBudget≤
        GeneralPaperSourceStaticConstructionRates.sourceProfile model W m k := hEnum.trans (Nat.le_add_right _ _)
    exact Nat.add_le_add hOwner hWhole
  · intro copied activeField activeLabel activeVariable activeBudget i
    have hEnum := GeneralPaperStaticEnumerationStorage.bounded W T m (prepare m k).K copied activeField activeLabel activeVariable activeBudget
    have hRow := GeneralPaperStaticRowConstructionStorage.bounded W copied hm prep.dictionary.label i
    have hWhole : GeneralPaperStaticEnumerationStorage.window W T m (prepare m k).K copied activeField activeLabel activeVariable activeBudget+
        GeneralPaperStaticRowConstructionStorage.window W copied prep.dictionary.label i≤
          GeneralPaperSourceStaticConstructionRates.sourceProfile model W m k := Nat.add_le_add hEnum hRow
    exact Nat.add_le_add ((hScans (some i)).trans hSum) hWhole

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
      StageAtBound model W k (GeneralPaperSourceStaticConstructionRates.reservation model W m k) prep inputs state hj := by
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

end Blotto.GeneralPaperSourceStaticConstructionStorage
