import Blotto.GeneralPaperSourceEndpointContinuationBits
import Blotto.GeneralPaperRetainedBitData

/-! Complete local bit price of the actual retained source endpoint:
guard, initializer/grid, native basis, affine cache, both final rechecks,
raw fraction copies and reached reciprocal. Source invariants discharge
all heights/magnitudes; address/control capacities remain explicit. -/
namespace Blotto.GeneralPaperSourceEndpointBitPrice
open GeneralPaperProxyParameters GeneralPaperBasisStoredProducts
open GeneralPaperRetainedBasisEndpoint (numerator denominator)
open GeneralPaperRetainedBasisEndpointBits
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem work_of_return {T m K S : ℕ} (model : RationalCostModel) (W H p q A B C : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) (hGuard : ¬(reciprocal=true ∧ value=0))
    (inputs : GeneralPaperSharedBasisInputs.Inputs T m K)
    (hInputs : (GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix).1=inputs)
    (state : GeneralPaperBasisState.State (m*(K-1)) (m*(K-1)))
    (hReturn : (GeneralPaperSharedBasisBits.run model W prep inputs).1=some state)
    (hA : (GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix).2≤A)
    (hB : (GeneralPaperSharedBasisBits.run model W prep inputs).2≤B)
    (hC : (continueRun model W prep.dictionary.label inputs.matrix S prep.threshold inputs.controls.auxiliary
      (if reciprocal then 1/value else value) inputs.betaN (numerator endpoint reciprocal)
      inputs.controls.N (denominator endpoint reciprocal) state).2≤C) :
    (run model W H p q reciprocal prep matrix endpoint value).2≤
      guardPrice model W value+A+B+C+endpointPrice model W endpoint value reciprocal+80*W := by
  rw [run,ite_eq_right hGuard]
  dsimp only
  rw [hInputs,hReturn]
  dsimp only
  omega

def profile (model : RationalCostModel) (W m k p q : ℕ) (reciprocal : Bool) : ℕ :=
  GeneralPaperRetainedBasisInputsPrice.bitProfile model W (prepare m k).H p q
    (GeneralPaperSourceScoreHeights.anchorHeight m k) m (prepare m k).K reciprocal+
  GeneralPaperBasisControllerBits.profile (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows
    m (prepare m k).K (prepare m k).S W
    (model.rat (GeneralPaperBasisBitEnvelope.width m k
      (GeneralPaperInitializerParameters.prepare m (prepare m k).H p q reciprocal).N (prepare m k).S
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows))+
  GeneralPaperSourceEndpointContinuationBits.profile model W m k+
  7*model.rat (GeneralPaperRetainedEndpointBitBounds.priceWidth (prepare m k).qbar)+144*W

theorem sum_bound (A B C g e P W : ℕ) (hg : g≤P+32*W) (he : e≤6*P+32*W) :
    g+A+B+C+e+80*W≤A+B+C+7*P+144*W := by omega

theorem actual_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field (prepare m k).K))
    (hMatrix : matrix=(GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth
      (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S).1)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
      (GeneralPaperProxyClassifier.classify m k b)).1
    (run model W (prepare m k).H f.num f.den reciprocal prep matrix endpoint
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).2≤profile model W m k f.num f.den reciprocal := by
  dsimp only
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let value := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k)
    (GeneralPaperProxyClassifier.classify m k b)).1
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
  have hValue := GeneralPaperEndpointRatioSize.height m k b hb hModify
  have hGuardPrice := GeneralPaperRetainedEndpointBitBounds.guard_price model W (prepare m k).qbar value hValue
  by_cases hGuard : reciprocal=true ∧ value=0
  · have hGuard' : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0 := hGuard
    rw [run,ite_eq_left hGuard']
    change guardPrice model W value≤profile model W m k f.num f.den reciprocal
    apply hGuardPrice.trans
    unfold profile
    omega
  · have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
    have hD := (binaryWordWidth_mono (show m*((prepare m k).K-1)+1≤m*((prepare m k).K-1)+3 by omega)).trans hDim
    have hInputData := GeneralPaperRetainedBasisInputs.actual_data true model W k f.num f.den reciprocal prep v matrix hMatrix hm hf.1 f.den_pos
    have hUnit := GeneralPaperSourceUnchangedDictionary.unit k Qv hm hQv weights hp hs b hb reciprocal
    have hInputsPrice := GeneralPaperRetainedBasisInputsPrice.bit_work model W (prepare m k).H f.num f.den
      (GeneralPaperSourceScoreHeights.anchorHeight m k) reciprocal prep matrix hm (H_positive m k) hf.1 f.den_pos
      (fun j l => ⟨hUnit.nonnegative j l,hUnit.bounded j l⟩)
      (GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal) hW hK hM hD
    have hBasisPrice := GeneralPaperSharedBasisBits.actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hW hDim hIndex hBatch hFinal
    obtain ⟨state,hReturn,hContinue⟩ := GeneralPaperSourceEndpointContinuationBits.actual_return model W k Qv hm hQv weights hp hs
      b hb reciprocal hModify hGuard hW hD hK hM hIndex
    have hBounds := GeneralPaperRetainedEndpointBitBounds.fraction_bounds model.rat W m k b hb hModify
    have hEndpointPrice := GeneralPaperRetainedEndpointBitBounds.endpoint_price model W (prepare m k).qbar endpoint value
      hBounds.1 hBounds.2 hValue reciprocal
    have hTotal := work_of_return model W (prepare m k).H f.num f.den _ _ _ reciprocal prep matrix endpoint value hGuard
      inputs hInputData state hReturn hInputsPrice hBasisPrice hContinue
    exact hTotal.trans (sum_bound _ _ _ _ _ _ _ hGuardPrice hEndpointPrice)

end Blotto.GeneralPaperSourceEndpointBitPrice
