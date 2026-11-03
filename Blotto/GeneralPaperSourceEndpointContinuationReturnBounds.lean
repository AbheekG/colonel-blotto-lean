import Blotto.GeneralPaperOuterEndpointFrameStorage

/-! Uniform actual continuation work, optional output and complete basis
ownership at the original source final invariant. These bounds retain the
native affine/raw-check sequence and do not assume successful acceptance. -/
namespace Blotto.GeneralPaperSourceEndpointContinuationReturnBounds
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperBasisState GeneralPaperBasisInvariant GeneralPaperBasisOriginalDirection
open GeneralPaperSourceFinalCheckStorage (endpointFraction)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceFinalEndpointReturnRates.affinePrice model W m k+
    GeneralPaperRawEndpointReturnStorage.price model W
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
      (GeneralPaperSourceFinalEndpointReturnRates.operandWidth m k)+16*W
def pointProfile (W m k : ℕ) : ℕ := GeneralPaperRawEndpointReturnStorage.optionProfile W (m*((prepare m k).K-1))
  (GeneralPaperSourceFinalEndpointReturnRates.operandWidth m k)

theorem source_bounds {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+1)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ state,Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state →
      let endpoint := endpointFraction model W m k b
      let result := GeneralPaperRetainedBasisEndpointBits.continueRun model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        inputs.controls.auxiliary (if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
          else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint) inputs.betaN
        (GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal) inputs.controls.N
        (GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal) state
      result.2≤price model W m k ∧ GeneralPaperRawEndpointReturnStorage.optionFoot W result.1≤pointProfile W m k ∧
        GeneralPaperEncodedBasisStorage.footprint W state≤GeneralPaperEncodedBasisStorage.paperProfile W m k := by
  dsimp only
  intro state inv
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let cache := GeneralPaperBasisAffineBits.prepare model.rat W state
  let endpoint := endpointFraction model W m k b
  let num := GeneralPaperRetainedBasisEndpoint.numerator endpoint reciprocal
  let den := GeneralPaperRetainedBasisEndpoint.denominator endpoint reciprocal
  let gamma := if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let H := (prepare m k).H
  let B := GeneralPaperSourceRawAffineStorage.numeratorCap m k
  let N := GeneralPaperSourceRawAffineStorage.denominatorCap m k inputs.controls.N
  let R := GeneralPaperSourceFinalEndpointReturnRates.operandWidth m k
  have hN : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hDetNZ : cache.determinant≠0 := inv.nonzero
  have hOut := GeneralPaperBasisAffineBits.invariant_output model.rat W hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid state inv
  have hPow := GeneralPaperBasisCacheSize.power_H m k (m*((prepare m k).K-1)) le_rfl
  have hDet : cache.determinant.natAbs≤H := hOut.1.trans hPow
  have hc (i) : (cache.constant.read i).natAbs≤H := (hOut.2 i).1.trans hPow
  have hs' (i) : (cache.slope.read i).natAbs≤H := (hOut.2 i).2.trans hPow
  have hBeta := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  change inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k at hBeta
  have hAN : inputs.betaN.natAbs≤B := hBeta.trans (Nat.le_add_right _ _)
  have hAD : inputs.controls.N≤N := Nat.le_add_right _ _
  have hEnd := GeneralPaperRetainedEndpointBitBounds.transformed_bounds model.rat W m k b hb hModify reciprocal
  have hEN : num.natAbs≤B := hEnd.1.trans (Nat.le_add_left _ _)
  have hED : den≤N := hEnd.2.trans (Nat.le_add_left _ _)
  have hValue : endpoint.value=(GeneralPaperProxyClassifier.classify m k b).choice.endpoint :=
    GeneralPaperRetainedEndpointFraction.actual_value model.rat W m k b
  have hDen : 0 < den := GeneralPaperRetainedBasisEndpoint.denominator_positive endpoint reciprocal _ hValue hGuard
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hAuxEq : (inputs.betaN:ℚ)/(inputs.controls.N:ℚ)=inputs.controls.auxiliary :=
    GeneralPaperBasisGridInputs.auxiliary_decode m H f.num f.den reciprocal hm (H_positive m k) hf.1 f.den_pos
  have hEndEq : (num:ℚ)/(den:ℚ)=(if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint) := GeneralPaperRetainedBasisEndpoint.represented endpoint reciprocal _ hValue
  have hGridWord := GeneralPaperSourceRayStorageWidth.grid_bound m k b hb reciprocal
  change binaryWordWidth inputs.controls.N≤GeneralPaperSourceRayStorageWidth.gridWord m k at hGridWord
  have hRaw : GeneralPaperRawAffineBits.width H B N≤R :=
    (GeneralPaperSourceRawAffineStorage.source_width m k inputs.controls.N hGridWord).trans (by
      unfold R GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceFinalCheckStorageRates.operandWidth
      omega)
  have hRoot := (GeneralPaperSourceFinalCheckStorage.source_widths m k inputs.controls.N (N*H) hGridWord le_rfl).1
  have hCache := GeneralPaperBasisCacheSize.cache_H k hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv
  have hConstant (i) := GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv i false
  have hSlope (i) := GeneralPaperBasisRowSize.rhs_entry hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
    inputs.betaN inputs.initialGrid le_rfl state inv i true
  have hBasis := GeneralPaperEncodedBasisStorage.invariant_bound W k hm prep.dictionary v (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid le_rfl state inv
  have hAffineR : GeneralPaperBasisAffineBits.width (m*((prepare m k).K-1)) H (m+1)≤R :=
    (GeneralPaperSourceBasisAffineStorage.operand_width m k).trans (by
      unfold R GeneralPaperSourceFinalEndpointReturnRates.operandWidth GeneralPaperSourceFinalCheckStorageRates.operandWidth
        GeneralPaperSourceRawAffineStorageRates.operandWidth GeneralPaperSourceBasisAffineStorageRates.operandWidth
        GeneralPaperSourceBasisCacheStorageRates.operandWidth
      omega)
  have hF : cache.work≤GeneralPaperSourceFinalEndpointReturnRates.affinePrice model W m k := by
    have h := GeneralPaperBasisAffineBits.work model.rat model.monotone W H (m+1) hW hDim state hCache.2 hCache.1 hConstant hSlope
    exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hAffineR) W))
  have hChecked := GeneralPaperRawEndpointReturnStorage.work model W H B N R hm prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
    inputs.controls.auxiliary gamma inputs.betaN num inputs.controls.N den hN hDen hAuxEq hEndEq
    cache hDetNZ hDet hc hs' hAN hAD hEN hED hRaw hRoot hW hDim hK hM hIndex
  have hPoint := GeneralPaperRawEndpointReturnStorage.option_bound model W H B N R prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
    inputs.controls.auxiliary gamma inputs.betaN num inputs.controls.N den cache hEN hED hDet hc hs' hRaw
  refine ⟨?_,hPoint,hBasis⟩
  change cache.work+(GeneralPaperRawEndpointBits.run model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
    inputs.controls.auxiliary gamma inputs.betaN num inputs.controls.N den cache).work+16*W≤price model W m k
  unfold price
  dsimp only [R] at hChecked
  omega

end Blotto.GeneralPaperSourceEndpointContinuationReturnBounds
