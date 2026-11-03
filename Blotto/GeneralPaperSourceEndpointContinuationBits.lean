import Blotto.GeneralPaperRetainedEndpointBitBounds

/-! The actual selected source and native basis return discharge every
affine-cache and final-check magnitude premise. This is the complete
local continuation profile, with original-row determinant envelopes and
actual constructed endpoint integers. Phase/global calibration is separate. -/
namespace Blotto.GeneralPaperSourceEndpointContinuationBits
open GeneralPaperProxyParameters GeneralPaperBasisStoredProducts GeneralPaperRetainedBasisEndpoint
open GeneralPaperRetainedBasisEndpointBits
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def gridCap (m k : ℕ) : ℕ := 4*m*(prepare m k).H*(prepare m k).qbar*(prepare m k).qbar
def determinantCap (m k : ℕ) : ℕ := (m+1)^(m*((prepare m k).K-1))

def profile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  let d := m*((prepare m k).K-1)
  let H := determinantCap m k
  let T := (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
  let Q := (prepare m k).qbar
  2048*(d+1)^2*(W+model.rat (GeneralPaperBasisAffineBits.width d H (m+1)))+
    GeneralPaperRawEndpointBits.evaluationProfile model W T m (prepare m k).K (prepare m k).S H
      (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (gridCap m k) (gridCap m k*H)+
    GeneralPaperRawEndpointBits.evaluationProfile model W T m (prepare m k).K (prepare m k).S H Q Q (Q*H)+32*W

theorem actual_return {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0))
    (hW : 1≤W) (hD : binaryWordWidth (m*((prepare m k).K-1)+1)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
      (GeneralPaperProxyClassifier.classify m k b)).1
    ∃ state,(GeneralPaperSharedBasisBits.run model W prep inputs).1=some state ∧
      (continueRun model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold inputs.controls.auxiliary
        (if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
          else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint)
        inputs.betaN (numerator endpoint reciprocal) inputs.controls.N (denominator endpoint reciprocal) state).2≤profile model W m k := by
  dsimp only
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
    (GeneralPaperProxyClassifier.classify m k b)).1
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  have hBasis : (GeneralPaperSharedBasisBits.run model W prep inputs).1=some state :=
    (GeneralPaperSharedBasisBits.data model W prep inputs).trans hr
  have hProxy := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hNum : f.num≤(prepare m k).qbar := hProxy.2.1.le.trans hProxy.2.2
  have hDen : f.den≤(prepare m k).qbar := hProxy.2.2
  have hN : inputs.controls.N≤gridCap m k :=
    Nat.mul_le_mul (Nat.mul_le_mul_left (4*m*(prepare m k).H) hNum) hDen
  have hAuxNum : inputs.betaN.natAbs≤GeneralPaperSourceBasisGridSize.auxiliaryBound m k :=
    GeneralPaperSourceBasisGridSize.auxiliary k b hb reciprocal
  have hAuxDen : 0 < inputs.controls.N := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hAux : (inputs.betaN:ℚ)/(inputs.controls.N:ℚ)=inputs.controls.auxiliary :=
    GeneralPaperBasisGridInputs.auxiliary_decode m (prepare m k).H f.num f.den reciprocal hm (H_positive m k)
      hProxy.1 (by have hh:=f.den_pos; exact hh)
  have hValue : endpoint.value=(GeneralPaperProxyClassifier.classify m k b).choice.endpoint :=
    GeneralPaperRetainedEndpointFraction.actual_value model.rat W m k b
  have hEndDen := denominator_positive endpoint reciprocal _ hValue hGuard
  have hEnd := represented endpoint reciprocal _ hValue
  have hBounds := GeneralPaperRetainedEndpointBitBounds.transformed_bounds model.rat W m k b hb hModify reciprocal
  have hWork := continue_work model W (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (gridCap m k)
    (prepare m k).qbar (prepare m k).qbar hm prep.dictionary v inputs.matrix (prepare m k).S prep.threshold
    inputs.controls.N inputs.betaN inputs.initialGrid state inv inputs.controls.auxiliary
    (if reciprocal then 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      else (GeneralPaperProxyClassifier.classify m k b).choice.endpoint)
    inputs.betaN (numerator endpoint reciprocal) inputs.controls.N (denominator endpoint reciprocal)
    hAuxDen hEndDen hAux hEnd hAuxNum hN hBounds.1 hBounds.2 hW hD hK hM hIndex
  have hDet : state.determinant.natAbs≤determinantCap m k :=
    GeneralPaperBasisCacheSize.determinant hm prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N
      inputs.betaN inputs.initialGrid (Nat.le_refl _) state inv
  have hAuxPrice := GeneralPaperRawEndpointBits.evaluationProfile_den_mono model W
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
    (determinantCap m k) (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) (gridCap m k) _ _ (Nat.mul_le_mul hN hDet)
  have hEndPrice := GeneralPaperRawEndpointBits.evaluationProfile_den_mono model W
    (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K (prepare m k).S
    (determinantCap m k) (prepare m k).qbar (prepare m k).qbar _ _ (Nat.mul_le_mul hBounds.2 hDet)
  refine ⟨state,hBasis,?_⟩
  exact hWork.trans (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add_left hAuxPrice _) hEndPrice) _)

end Blotto.GeneralPaperSourceEndpointContinuationBits
