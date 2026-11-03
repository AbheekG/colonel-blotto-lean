import Blotto.GeneralPaperRetainedBasisInputsPrice
import Blotto.GeneralPaperCheckedBasisEndpoint

/-! Native arithmetic endpoint continuation from a retained prepared
dictionary and score matrix. Initializer, basis and affine cache each run
once; explicit constructed raw fractions feed the final checks. The zero
reciprocal guard precedes all those calls. This module does not claim the
bit price of affine-cache construction or the final checks. -/
namespace Blotto.GeneralPaperRetainedBasisEndpoint
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 4500000

def numerator (endpoint : Farey.Fraction) (reciprocal : Bool) : ℤ :=
  if reciprocal then endpoint.den else endpoint.num

def denominator (endpoint : Farey.Fraction) (reciprocal : Bool) : ℕ :=
  if reciprocal then endpoint.num else endpoint.den

theorem denominator_positive (endpoint : Farey.Fraction) (reciprocal : Bool) (value : ℚ)
    (hValue : endpoint.value=value) (hGuard : ¬(reciprocal=true ∧ value=0)) :
    0<denominator endpoint reciprocal := by
  cases reciprocal with
  | false => exact endpoint.den_pos
  | true =>
    have hn : endpoint.num≠0 := by
      intro hz
      apply hGuard
      refine ⟨rfl,?_⟩
      rw [←hValue,Farey.Fraction.value,hz,Nat.cast_zero,zero_div]
    exact Nat.pos_of_ne_zero hn

theorem represented (endpoint : Farey.Fraction) (reciprocal : Bool) (value : ℚ)
    (hValue : endpoint.value=value) :
    (numerator endpoint reciprocal:ℚ)/(denominator endpoint reciprocal:ℚ)=
      (if reciprocal then 1/value else value) := by
  cases reciprocal with
  | false => simpa only [numerator,denominator,Bool.false_eq_true,ite_false,Int.cast_natCast,Farey.Fraction.value] using hValue
  | true =>
    simp only [numerator,denominator,ite_true,Int.cast_natCast,←hValue,Farey.Fraction.value,one_div,inv_div]

def run {T m K S : ℕ} (model : RationalCostModel) (H p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m K S) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (endpoint : Farey.Fraction) (value : ℚ) : Option (GeneralPaperBasisRationalSolve.RatVector (m*(K-1)))×ℕ :=
  if reciprocal=true ∧ value=0 then (none,32) else
    let inputs := GeneralPaperRetainedBasisInputs.run false model 1 H p q reciprocal prep matrix
    let basis := GeneralPaperSharedBasisWork.run prep inputs.1
    match basis.1 with
    | none => (none,inputs.2+basis.2+64)
    | some state =>
      let affine := GeneralPaperBasisAffineData.prepare state
      let gamma : ℚ := if reciprocal then 1/value else value
      let checked := GeneralPaperRawAffineEndpoint.run false model 1 prep.dictionary.label inputs.1.matrix S prep.threshold
        inputs.1.controls.auxiliary gamma inputs.1.betaN (numerator endpoint reciprocal)
        inputs.1.controls.N (denominator endpoint reciprocal) affine
      (checked.point,inputs.2+basis.2+affine.work+checked.work+80)

theorem data {T m : ℕ} (model : RationalCostModel) (k p q : ℕ) (reciprocal : Bool)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field (prepare m k).K))
    (hMatrix : matrix=(GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v (prepare m k).S).1)
    (endpoint : Farey.Fraction) (value : ℚ) (hValue : endpoint.value=value)
    (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    (run model (prepare m k).H p q reciprocal prep matrix endpoint value).1=
      GeneralPaperCheckedBasisEndpoint.run k prep v p q value reciprocal := by
  let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
  have hi := GeneralPaperRetainedBasisInputs.actual_data false model 1 k p q reciprocal prep v matrix hMatrix hm hp hq
  have hAuxDen : 0 < inputs.controls.N :=
    GeneralPaperInitializerParameters.N_positive m (prepare m k).H p q reciprocal hm (H_positive m k) hp hq
  have hAux : (inputs.betaN:ℚ)/(inputs.controls.N:ℚ)=inputs.controls.auxiliary :=
    GeneralPaperBasisGridInputs.auxiliary_decode m (prepare m k).H p q reciprocal hm (H_positive m k) hp hq
  simp only [run,GeneralPaperCheckedBasisEndpoint.run]
  split
  · rfl
  · rename_i hGuard
    rw [hi,GeneralPaperSharedBasisWork.data]
    cases hb : GeneralPaperSharedBasisInputs.basis prep inputs with
    | none => rfl
    | some state =>
      exact GeneralPaperRawAffineEndpoint.point false model 1 prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        inputs.controls.auxiliary (if reciprocal then 1/value else value) inputs.betaN (numerator endpoint reciprocal)
        inputs.controls.N (denominator endpoint reciprocal) hAuxDen (denominator_positive endpoint reciprocal value hValue hGuard)
        hAux (represented endpoint reciprocal value hValue) (GeneralPaperBasisAffineData.prepare state)

end Blotto.GeneralPaperRetainedBasisEndpoint
