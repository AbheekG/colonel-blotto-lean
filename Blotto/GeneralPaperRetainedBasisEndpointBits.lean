import Blotto.GeneralPaperRawEndpointBits
import Blotto.GeneralPaperRetainedBasisEndpoint
import Blotto.GeneralPaperSharedBasisBits

/-! Once-only bit-priced endpoint continuation. The retained matrix is
passed through initializer, basis, affine cache and both final checks.
The reciprocal-zero guard precedes all those calls. Costs of comparisons,
raw fraction copies and the reached reciprocal are included explicitly. -/
namespace Blotto.GeneralPaperRetainedBasisEndpointBits
open GeneralPaperProxyParameters GeneralPaperBasisStoredProducts GeneralPaperBasisState
open GeneralPaperRetainedBasisEndpoint
set_option autoImplicit false
set_option maxHeartbeats 6000000

def continueRun {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (state : State (m*(K-1)) (m*(K-1))) : Option (GeneralPaperBasisRationalSolve.RatVector (m*(K-1)))×ℕ :=
  let affine := GeneralPaperBasisAffineBits.prepare model.rat W state
  let checked := GeneralPaperRawEndpointBits.run model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen affine
  (checked.point,affine.work+checked.work+16*W)

theorem continue_data {T m K : ℕ} (model : RationalCostModel) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen)
    (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (state : State (m*(K-1)) (m*(K-1))) :
    (continueRun model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen state).1=
      (GeneralPaperCheckedAffineEndpoint.run labels matrix S h auxiliary gamma (GeneralPaperBasisAffineData.prepare state)).point := by
  dsimp only [continueRun]
  rw [GeneralPaperRawEndpointBits.cache_congr model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen
    (GeneralPaperBasisAffineBits.prepare model.rat W state) (GeneralPaperBasisAffineData.prepare state)
    (GeneralPaperBasisAffineBits.constant model.rat W state) (GeneralPaperBasisAffineBits.slope model.rat W state) rfl]
  exact GeneralPaperRawEndpointBits.represented model W labels matrix S h auxiliary gamma auxNum endNum auxDen endDen
    hAuxDen hEndDen hAux hEnd _

theorem continue_work {T m K : ℕ} (model : RationalCostModel) (W Ba Na Be Ne : ℕ) (hm : 0<m)
    (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h N : ℕ) (betaN : ℤ)
    (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : GeneralPaperBasisInvariant.Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state)
    (auxiliary gamma : ℚ) (auxNum endNum : ℤ) (auxDen endDen : ℕ)
    (hAuxDen : 0<auxDen) (hEndDen : 0<endDen)
    (hAux : (auxNum:ℚ)/(auxDen:ℚ)=auxiliary) (hEnd : (endNum:ℚ)/(endDen:ℚ)=gamma)
    (hAN : auxNum.natAbs≤Ba) (hAD : auxDen≤Na) (hEN : endNum.natAbs≤Be) (hED : endDen≤Ne)
    (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W) (hK : binaryWordWidth (K+1)≤W)
    (hM : binaryWordWidth (m+1)≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (continueRun model W dict.label matrix S h auxiliary gamma auxNum endNum auxDen endDen state).2≤
      2048*(m*(K-1)+1)^2*(W+model.rat
        (GeneralPaperBasisAffineBits.width (m*(K-1)) ((m+1)^(m*(K-1))) (m+1)))+
      GeneralPaperRawEndpointBits.evaluationProfile model W T m K S ((m+1)^(m*(K-1))) Ba Na (auxDen*state.determinant.natAbs)+
      GeneralPaperRawEndpointBits.evaluationProfile model W T m K S ((m+1)^(m*(K-1))) Be Ne (endDen*state.determinant.natAbs)+32*W := by
  let affine := GeneralPaperBasisAffineBits.prepare model.rat W state
  have hCache := GeneralPaperBasisAffineBits.invariant_work model.rat model.monotone W hW hD hm dict v S h N betaN initialGrid state inv
  have hOut := GeneralPaperBasisAffineBits.invariant_output model.rat W hm dict v S h N betaN initialGrid state inv
  have hCheck := GeneralPaperRawEndpointBits.work model W ((m+1)^(m*(K-1))) Ba Na Be Ne hm dict.label matrix S h
    auxiliary gamma auxNum endNum auxDen endDen hAuxDen hEndDen hAux hEnd affine inv.nonzero
    hOut.1 (fun i => (hOut.2 i).1) (fun i => (hOut.2 i).2) hAN hAD hEN hED hW hD hK hM hIndex
  change affine.work≤_ at hCache
  change affine.work+(GeneralPaperRawEndpointBits.run model W dict.label matrix S h auxiliary gamma
    auxNum endNum auxDen endDen affine).work+16*W≤_
  change _≤GeneralPaperRawEndpointBits.evaluationProfile model W T m K S ((m+1)^(m*(K-1))) Ba Na (auxDen*state.determinant.natAbs)+
    GeneralPaperRawEndpointBits.evaluationProfile model W T m K S ((m+1)^(m*(K-1))) Be Ne (endDen*state.determinant.natAbs)+16*W at hCheck
  omega

def guardPrice (model : RationalCostModel) (W : ℕ) (value : ℚ) : ℕ :=
  model.rat (RationalExpression.pairWidth value 0)+32*W

def endpointPrice (model : RationalCostModel) (W : ℕ) (endpoint : Farey.Fraction) (value : ℚ) (reciprocal : Bool) : ℕ :=
  model.rat (1+binaryWordWidth endpoint.num)+model.rat (1+binaryWordWidth endpoint.den)+
  model.rat (GeneralPaperIntegerPrimitivePrice.word (numerator endpoint reciprocal))+
  model.rat (1+binaryWordWidth (denominator endpoint reciprocal))+
  (if reciprocal then GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x/y) 1 value
    else model.rat (rationalWordWidth value))+32*W

def run {T m K S : ℕ} (model : RationalCostModel) (W H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) : Option (GeneralPaperBasisRationalSolve.RatVector (m*(K-1)))×ℕ :=
  let guard := guardPrice model W value
  if reciprocal=true ∧ value=0 then (none,guard) else
    let inputs := GeneralPaperRetainedBasisInputs.run true model W H p q reciprocal prep matrix
    let basis := GeneralPaperSharedBasisBits.run model W prep inputs.1
    match basis.1 with
    | none => (none,guard+inputs.2+basis.2+64*W)
    | some state =>
      let gamma : ℚ := if reciprocal then 1/value else value
      let checked := continueRun model W prep.dictionary.label inputs.1.matrix S prep.threshold
        inputs.1.controls.auxiliary gamma inputs.1.betaN (numerator endpoint reciprocal)
        inputs.1.controls.N (denominator endpoint reciprocal) state
      (checked.1,guard+inputs.2+basis.2+checked.2+endpointPrice model W endpoint value reciprocal+80*W)

theorem data {T m : ℕ} (model : RationalCostModel) (W k p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field (prepare m k).K))
    (hMatrix : matrix=(GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v (prepare m k).S).1)
    (endpoint : Farey.Fraction) (value : ℚ) (hValue : endpoint.value=value)
    (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    (run model W (prepare m k).H p q reciprocal prep matrix endpoint value).1=
      GeneralPaperCheckedBasisEndpoint.run k prep v p q value reciprocal := by
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
  have hi := GeneralPaperRetainedBasisInputs.actual_data true model W k p q reciprocal prep v matrix hMatrix hm hp hq
  have hAuxDen : 0 < inputs.controls.N :=
    GeneralPaperInitializerParameters.N_positive m (prepare m k).H p q reciprocal hm (H_positive m k) hp hq
  have hAux : (inputs.betaN:ℚ)/(inputs.controls.N:ℚ)=inputs.controls.auxiliary :=
    GeneralPaperBasisGridInputs.auxiliary_decode m (prepare m k).H p q reciprocal hm (H_positive m k) hp hq
  simp only [run,GeneralPaperCheckedBasisEndpoint.run]
  split
  · rfl
  · rename_i hGuard
    rw [hi,GeneralPaperSharedBasisBits.data]
    cases hb : GeneralPaperSharedBasisInputs.basis prep inputs with
    | none => rfl
    | some state =>
      exact continue_data model W prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        inputs.controls.auxiliary (if reciprocal then 1/value else value) inputs.betaN (numerator endpoint reciprocal)
        inputs.controls.N (denominator endpoint reciprocal) hAuxDen (denominator_positive endpoint reciprocal value hValue hGuard)
        hAux (represented endpoint reciprocal value hValue) state

end Blotto.GeneralPaperRetainedBasisEndpointBits
