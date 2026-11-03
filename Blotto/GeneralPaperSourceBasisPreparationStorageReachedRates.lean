import Blotto.GeneralPaperSourceBasisPreparationStorage

/-! Literal actual common-word bound for complete native point/direction
preparation windows at reached source states, preserving retained RHS/
products/basis/grid and all earlier phase contracts. Division, assembly,
solve and full preparation returns coexist. Basis advance/update/final-check,
enclosing controller/source lifetimes and global calibration remain open. -/
namespace Blotto.GeneralPaperSourceBasisPreparationStorageReachedRates
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
        (_hW : 1≤W) (_hK : binaryWordWidth ((prepare z.m z.k).K+1)≤W) (_hM : binaryWordWidth (z.m+1)≤W)
        (_hIndex : binaryWordWidth ((prepare z.m z.k).S+2)≤W) (_hDim : binaryWordWidth (z.m*((prepare z.m z.k).K-1)+1)≤W)
        (_hBatch : binaryWordWidth (((prepare z.m z.k).S+1)*((prepare z.m z.k).K*(prepare z.m z.k).K)+3)≤W)
        (_hFinalIndex : binaryWordWidth ((prepare z.m z.k).S+4)≤W)
        (j : ℕ) (hj : j<z.m*((prepare z.m z.k).K-1)),
        let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
        let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare z.m z.k).S prep.threshold
          inputs.controls.N inputs.betaN inputs.initialGrid j (Nat.le_of_lt hj)).1=some state ∧
          GeneralPaperSourceBasisPreparationStorage.StageAtBound model W z.k
            (A*(z.m+1)^3*2^(4*z.k)*(logSize z)^e) prep inputs state hj := by
  obtain ⟨A,e,hRate⟩ := GeneralPaperSourceBasisPreparationStorageRates.actual_common_word hg
  refine ⟨A,e,?_⟩
  intro z
  dsimp only
  intro Qv hm hQv weights hp hs b hb reciprocal hW hK hM hIndex hDim hBatch hFinalIndex j hj
  let W := GeneralPaperCompilerReference.width C d z
  let prep := GeneralPaperSourceInitializer.prepared z.k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
  obtain ⟨state,hr,hBound⟩ := GeneralPaperSourceBasisPreparationStorage.actual_reached model W z.k Qv hm hQv weights hp hs b hb reciprocal
    hW hK hM hIndex hDim hBatch hFinalIndex j hj
  refine ⟨state,hr,?_⟩
  exact GeneralPaperSourceBasisPreparationStorage.stage_mono model W z.k prep inputs state hj _ _ (hRate z) hBound

end Blotto.GeneralPaperSourceBasisPreparationStorageReachedRates
