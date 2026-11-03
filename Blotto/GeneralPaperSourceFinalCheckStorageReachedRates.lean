import Blotto.GeneralPaperSourceFinalCheckStorage

/-! Actual common-word bound for both complete final static/strict-score
DP feasibility checks at reached source states. Original raw lattices and
magnitudes hold before acceptance, and the existing reciprocal-zero guard
supplies the endpoint denominator. All preceding contracts remain. Parent
endpoint returns, initialization/controller/source lifetimes and global
capacity calibration remain open. -/
namespace Blotto.GeneralPaperSourceFinalCheckStorageReachedRates
open GeneralPaperSourceWordGrowth GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

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
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W) (_hDim : binaryWordWidth (z.m*((prepare z.m z.k).K-1)+1)≤W)
        (_hBatch : binaryWordWidth (((prepare z.m z.k).S+1)*((prepare z.m z.k).K*(prepare z.m z.k).K)+3)≤W)
        (_hFinalIndex : binaryWordWidth ((prepare z.m z.k).S+4)≤W),
        let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
        let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare z.m z.k).S prep.threshold
          inputs.controls.N inputs.betaN inputs.initialGrid (z.m*((prepare z.m z.k).K-1)) le_rfl).1=some state ∧
          GeneralPaperSourceFinalCheckStorage.AtBound model W z.k
            (A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e) b reciprocal prep inputs state := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceFinalCheckStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro Qv hm hQv weights hp hs b hb reciprocal hModify hGuard hW hK hM hIndex hDim hBatch hFinalIndex
  let W := GeneralPaperCompilerReference.width C d z
  let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
  obtain ⟨state,hr,hBound⟩ := GeneralPaperSourceFinalCheckStorage.actual_reached model W z.k Qv hm hQv weights hp hs b hb reciprocal hModify hGuard
    hW hK hM hIndex hDim hBatch hFinalIndex
  refine ⟨state,hr,?_⟩
  exact GeneralPaperSourceFinalCheckStorage.bound_mono model W z.k b reciprocal prep inputs state _ _ (hRate z) hBound

end Blotto.GeneralPaperSourceFinalCheckStorageReachedRates
