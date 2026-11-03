import Blotto.GeneralPaperSourceBasisGridPackingStorageRates

/-! Complete actual source grid packing. Values are the original native
stored quotients projected from the shared table, not a reconstructed floor.
Source N/unit facts derive every value word. Full table constructor windows
coexist with enumeration/entry/zero-fill/write/parent packing windows. -/
namespace Blotto.GeneralPaperSourceBasisGridPackingStorage
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperEncodedBasisStorage (integerBits)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def values {T m : ℕ} (model : RationalCostModel) (W k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K) : Variable m (prepare m k).K → ℤ :=
  GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W inputs.controls.N inputs.controls.depth prep.dictionary.anchor).1

def window {T m : ℕ} (model : RationalCostModel) (W k zeroCopied enumerationCopied : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (activeField : Option (Fin m)) (activeLabel : Option (Fin ((prepare m k).K-1))) : ℕ :=
  GeneralPaperBasisGridPackingStorage.window model W zeroCopied enumerationCopied (values model W k prep inputs) activeField activeLabel

def AtBound {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) : Prop :=
  ∃ previousReserve packingReserve,GeneralPaperSourceInitializerTableStorage.AtBound model W k previousReserve b reciprocal prep inputs state ∧
    (∀ z e af al,window model W k z e prep inputs af al≤packingReserve) ∧ previousReserve+packingReserve≤limit

theorem bound_mono {T m : ℕ} (model : RationalCostModel) (W k : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1))) (B C : ℕ) (hBC : B≤C)
    (h : AtBound model W k B b reciprocal prep inputs state) : AtBound model W k C b reciprocal prep inputs state := by
  obtain ⟨D,F,hPrevious,hPacking,hSum⟩ := h
  exact ⟨D,F,hPrevious,hPacking,hSum.trans hBC⟩

theorem retained_table {T m : ℕ} (model : RationalCostModel) (W k limit : ℕ) (b : ℝ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m (prepare m k).K)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (h : AtBound model W k limit b reciprocal prep inputs state) :
    ∀ o i z e af al,GeneralPaperSourceInitializerTableStorage.window model W k o i prep inputs+
      window model W k z e prep inputs af al≤limit := by
  obtain ⟨D,F,⟨D0,F0,_,hTable,hOldSum⟩,hPacking,hSum⟩ := h
  intro o i z e af al
  exact (Nat.add_le_add ((hTable o i).trans (show F0≤D by omega)) (hPacking z e af al)).trans hSum

theorem source_packing {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) (hW : 1≤W)
    (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ z e af al,window model W k z e prep inputs af al≤GeneralPaperSourceBasisGridPackingStorageRates.sourceProfile model W m k := by
  dsimp only
  intro z e af al
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let R := GeneralPaperSourceBasisGridPackingStorageRates.operandWidth m k
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hCap : inputs.controls.N<2^inputs.controls.depth := GeneralPaperInitializerParameters.quotient_cap m (prepare m k).H f.num f.den reciprocal
  have hUnit := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb reciprocal
  have hAbs : ∀ a,(values model W k prep inputs a).natAbs≤ inputs.controls.N :=
    GeneralPaperInitializerGridPrice.values_bound model W inputs.controls.N inputs.controls.depth prep.dictionary hN hCap
      (fun j l => ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩)
  have hGrid := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGrid
  have hValues : ∀ a,integerBits (values model W k prep inputs a)≤R := by
    intro a
    exact (Nat.add_le_add_left (binaryWordWidth_mono (hAbs a)) 1).trans (Nat.add_le_add_left hGrid 1)
  have hR : 2≤R := by unfold R GeneralPaperSourceBasisGridPackingStorageRates.operandWidth GeneralPaperSourceRayStorageWidth.gridWord; omega
  exact GeneralPaperBasisGridPackingStorage.bounded model W R z e (values model W k prep inputs) hValues hR hW hDim af al

theorem source_stage {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      AtBound model W k (GeneralPaperSourceBasisGridPackingStorageRates.reservation model W m k) b reciprocal prep inputs state := by
  dsimp only
  intro state inv
  have hOld := GeneralPaperSourceInitializerTableStorage.source_stage model W k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex state inv
  have hDim1 := (binaryWordWidth_mono (show m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3 by omega)).trans hDim
  exact ⟨GeneralPaperSourceInitializerTableStorageRates.reservation model W m k,
    GeneralPaperSourceBasisGridPackingStorageRates.sourceProfile model W m k,hOld,
    source_packing model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim1,le_rfl⟩

theorem actual_reached {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinalIndex : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.N inputs.betaN inputs.initialGrid (m*((prepare m k).K-1)) le_rfl).1=some state ∧
      AtBound model W k (GeneralPaperSourceBasisGridPackingStorageRates.reservation model W m k) b reciprocal prep inputs state := by
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

end Blotto.GeneralPaperSourceBasisGridPackingStorage
