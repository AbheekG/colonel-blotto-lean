import Blotto.GeneralPaperEndpointRecheckWork

/-! The shared basis execution keeps its matrix and cache live through
both prescribed rechecks. Exact original initializer controls supply the
auxiliary point. Correct inputs pass both guards and return the SAME
native rational endpoint as the unchecked mathematical core.
-/
namespace Blotto.GeneralPaperCheckedBasisEndpoint
open RationalOrderCell GeneralPaperProxyParameters GeneralPaperBasisInvariant GeneralPaperBasisState
open GeneralPaperBasisOriginalDirection
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {T m : ℕ} (k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (endpoint : ℚ) (reciprocal : Bool) :
    Option (GeneralPaperBasisRationalSolve.RatVector (m*((prepare m k).K-1))) :=
  if reciprocal=true ∧ endpoint=0 then none else
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
    (GeneralPaperSharedBasisInputs.basis prep inputs).bind (fun state =>
      let gamma : ℚ := if reciprocal then 1/endpoint else endpoint
      (GeneralPaperEndpointRecheckWork.run prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
        inputs.controls.auxiliary gamma state).point)

theorem auxiliary_feasible {T m : ℕ} (k : ℕ) (hm : 0<m)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (hp : 0<p) (hq : 0<q) (reciprocal : Bool)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state) :
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
    GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S)
      prep.threshold (inputs.controls.auxiliary:ℝ)
      (fun a => (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) inputs.controls.auxiliary).1 a:ℝ)) := by
  have hn := GeneralPaperInitializerParameters.N_positive m (prepare m k).H p q reciprocal hm (H_positive m k) hp hq
  have hRatio :
      (GeneralPaperBasisGridInputs.auxiliaryNumerator m (prepare m k).H p q reciprocal:ℝ)/
        ((GeneralPaperInitializerParameters.prepare m (prepare m k).H p q reciprocal).N:ℝ)=
      ((GeneralPaperInitializerParameters.prepare m (prepare m k).H p q reciprocal).auxiliary:ℝ) := by
    have hh := congrArg (fun r : ℚ => (r:ℝ))
      (GeneralPaperBasisGridInputs.auxiliary_decode m (prepare m k).H p q reciprocal hm (H_positive m k) hp hq)
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using hh
  have hAux := GeneralPaperBasisAffineOriginal.initial_feasible prep.dictionary v (prepare m k).S prep.threshold
    _ hn _ _ state inv
  dsimp only [GeneralPaperSharedBasisInputs.prepare] at hAux
  rw [hRatio] at hAux
  exact GeneralPaperSourceBasisEndpoint.evaluated_feasible prep.dictionary v (prepare m k).S prep.threshold state inv.nonzero _ hAux

theorem accepted {T m : ℕ} (k : ℕ) (hm : 0<m)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (hp : 0<p) (hq : 0<q) (reciprocal : Bool)
    (state : State (m*((prepare m k).K-1)) (m*((prepare m k).K-1)))
    (inv : let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state)
    (gamma : ℚ)
    (hEnd : GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S)
      prep.threshold (gamma:ℝ)
      (fun a => (reader (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a:ℝ))) :
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal
    (GeneralPaperCheckedAffineEndpoint.run prep.dictionary.label inputs.matrix (prepare m k).S prep.threshold
      inputs.controls.auxiliary gamma (GeneralPaperBasisAffineData.prepare state)).point=
        some (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 := by
  have hh := GeneralPaperCheckedAffineEndpoint.accepted (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary v
    (prepare m k).S prep.threshold (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
    (GeneralPaperSharedBasisInputs.prepare k prep v p q reciprocal).controls.auxiliary gamma (GeneralPaperBasisAffineData.prepare state)
    (auxiliary_feasible k hm prep v p q hp hq reciprocal state inv) hEnd
  rw [←GeneralPaperSharedBasisInputs.matrix_eq k prep v p q reciprocal] at hh
  exact hh

end Blotto.GeneralPaperCheckedBasisEndpoint
