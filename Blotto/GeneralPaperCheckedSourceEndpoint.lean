import Blotto.GeneralPaperCheckedBasisEndpoint

/-! For the actual full source, both prescribed final checks accept.
The checked compiler returns exactly the existing rational endpoint,
while executing the checks before discarding the shared basis/matrix.
-/
namespace Blotto.GeneralPaperCheckedSourceEndpoint
open GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :=
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  GeneralPaperCheckedBasisEndpoint.run k prep (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    f.num f.den (GeneralPaperProxyClassifier.classify m k b).choice.endpoint reciprocal

theorem prepared_run_source {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    GeneralPaperCheckedBasisEndpoint.run k (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal)
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint reciprocal=
        run k Qv hQv weights hp hs b reciprocal := rfl

theorem rich_eq {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    run k Qv hQv weights hp hs b false=GeneralPaperSourceBasisEndpoint.run k Qv hQv weights hp hs b false := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  obtain ⟨state,hRun,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb false
  have hOld : GeneralPaperSourceBasis.run k Qv hQv weights hp hs b false=some state := hRun
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hCont := GeneralPaperBasisEndpointContinuation.rich k hm prep.dictionary v (prepare m k).S prep.threshold _
    (positive m k hm b hb false).1 _ _ state inv b hb hModify
    (GeneralPaperBasisContinuationControls.auxiliary_value m k hm b hb false)
  have hEval := GeneralPaperSourceBasisEndpoint.evaluated_feasible prep.dictionary v (prepare m k).S prep.threshold
    state inv.nonzero (GeneralPaperProxyClassifier.classify m k b).choice.endpoint hCont
  have hCheck := GeneralPaperCheckedBasisEndpoint.accepted k hm prep v f.num f.den hf.1 f.den_pos false state inv
    (GeneralPaperProxyClassifier.classify m k b).choice.endpoint hEval
  dsimp only [prep,v,f] at hCheck
  calc
    _ = some (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state)
        (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).1 := by
      simp only [run,GeneralPaperCheckedBasisEndpoint.run,Bool.false_eq_true,false_and,ite_false,hRun,Option.bind_some,
        GeneralPaperEndpointRecheckWork.point,hCheck]
    _ = _ := by
      symm
      simp only [GeneralPaperSourceBasisEndpoint.run,Bool.false_eq_true,false_and,ite_false,hOld,Option.map_some]

theorem poor_eq {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hEndpoint : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    run k Qv hQv weights hp hs b true=GeneralPaperSourceBasisEndpoint.run k Qv hQv weights hp hs b true := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  let gamma : ℚ := 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  obtain ⟨state,hRun,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb true
  have hOld : GeneralPaperSourceBasis.run k Qv hQv weights hp hs b true=some state := hRun
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hCont := GeneralPaperBasisEndpointContinuation.poor k hm prep.dictionary v (prepare m k).S prep.threshold _
    (positive m k hm b hb true).1 _ _ state inv b hb hModify hEndpoint
    (GeneralPaperBasisContinuationControls.auxiliary_value m k hm b hb true)
  have hRat : GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label (GeneralPaperStrictScore.score v (prepare m k).S)
      prep.threshold (gamma:ℝ) (fun a => GeneralPaperBasisAffineSystem.value (GeneralPaperBasisAffineData.prepare state) (gamma:ℝ)
        (GeneralPaperBasisCoordinates.index a)) := by
    simpa only [gamma,Rat.cast_div,Rat.cast_one] using hCont
  have hEval := GeneralPaperSourceBasisEndpoint.evaluated_feasible prep.dictionary v (prepare m k).S prep.threshold
    state inv.nonzero gamma hRat
  have hCheck := GeneralPaperCheckedBasisEndpoint.accepted k hm prep v f.num f.den hf.1 f.den_pos true state inv gamma hEval
  dsimp only [prep,v,f,gamma] at hCheck
  have he : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint≠0 := by exact_mod_cast hEndpoint.ne'
  calc
    _ = some (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 := by
      simp only [run,GeneralPaperCheckedBasisEndpoint.run,he,and_false,ite_false,ite_true,hRun,Option.bind_some,
        GeneralPaperEndpointRecheckWork.point,hCheck,gamma]
    _ = _ := by
      symm
      simp only [GeneralPaperSourceBasisEndpoint.run,he,and_false,ite_false,ite_true,hOld,Option.map_some,gamma]

end Blotto.GeneralPaperCheckedSourceEndpoint
