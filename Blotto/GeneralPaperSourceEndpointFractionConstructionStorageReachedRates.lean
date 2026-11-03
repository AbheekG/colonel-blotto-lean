import Blotto.GeneralPaperSourceEndpointFractionConstructionStorage

/-! Common-word bounds for full native endpoint-fraction construction,
all earlier native endpoint phases and guard rejection. Constructor storage
and work are derived for all classifier branches without child premises. -/
namespace Blotto.GeneralPaperSourceEndpointFractionConstructionStorageReachedRates
open GeneralPaperSourceWordGrowth GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem actual_reached_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (Qv : ℕ) (_hm : 0<z.m) (hQv : 0<Qv)
        (weights : FixedArrayTable z.m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0))
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W)
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W) (_hDim : binaryWordWidth (z.m*((prepare z.m z.k).K-1)+3)≤W)
        (_hBatch : binaryWordWidth (((prepare z.m z.k).S+1)*((prepare z.m z.k).K*(prepare z.m z.k).K)+3)≤W)
        (_hFinalIndex : binaryWordWidth ((prepare z.m z.k).S+4)≤W),
        let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
        let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare z.m z.k).S prep.threshold
          inputs.controls.N inputs.betaN inputs.initialGrid (z.m*((prepare z.m z.k).K-1)) le_rfl).1=some state ∧
          GeneralPaperSourceEndpointFractionConstructionStorage.AtBound model W z.k
            (A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e) b reciprocal prep inputs state := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceEndpointFractionConstructionStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro Qv hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hFinalIndex
  let W := GeneralPaperCompilerReference.width C d z
  let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
  obtain ⟨state,hr,hBound⟩ := GeneralPaperSourceEndpointFractionConstructionStorage.actual_reached model W z.k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  refine ⟨state,hr,?_⟩
  exact GeneralPaperSourceEndpointFractionConstructionStorage.bound_mono model W z.k b reciprocal prep inputs state _ _ (hRate z) hBound

theorem constructor_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,∀ (b : ℝ),0<b ∧ b<1 →
      GeneralPaperSourceEndpointFractionConstructionStorage.window model (GeneralPaperCompilerReference.width C d z) z.m z.k b≤
        A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceEndpointFractionConstructionStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z b hb
  have h := (GeneralPaperSourceEndpointFractionConstructionStorage.source_constructor model (GeneralPaperCompilerReference.width C d z) z.m z.k b hb).1
  exact h.trans ((Nat.le_add_left _ _).trans (hRate z))

theorem guard_common_word {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ z : Input,
      let W := GeneralPaperCompilerReference.width C d z
      ∀ (Qv : ℕ) (_hm : 0<z.m) (hQv : 0<Qv)
        (weights : FixedArrayTable z.m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0),
        let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
        let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        GeneralPaperSourceOuterEndpointStorage.window model W z.k b reciprocal prep inputs+
          GeneralPaperSourceEndpointFractionConstructionStorage.window model W z.m z.k b≤A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceEndpointFractionConstructionStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
  exact (GeneralPaperSourceEndpointFractionConstructionStorage.source_guard model (GeneralPaperCompilerReference.width C d z)
    z.k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard).trans (hRate z)

end Blotto.GeneralPaperSourceEndpointFractionConstructionStorageReachedRates
