import Blotto.GeneralPaperBasisEndpointContinuation

/-! Actual full source-to-native-endpoint point, for the two positive
endpoint branches. The poor zero endpoint is guarded BEFORE reciprocal
evaluation and remains the separate maximal-score branch.
-/
namespace Blotto.GeneralPaperSourceBasisEndpoint
open RationalOrderCell GeneralPaperStrictScore GeneralPaperProxyParameters GeneralPaperInitializerSelectedControls
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisCoordinates
set_option autoImplicit false
set_option maxHeartbeats 4500000

def preparedRun {T m : ℕ} (k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (endpoint : ℚ) (reciprocal : Bool) :
    Option (GeneralPaperBasisRationalSolve.RatVector (m*((prepare m k).K-1))) :=
  if reciprocal=true ∧ endpoint=0 then none else
    (GeneralPaperSourceBasis.fromPrepared k prep v p q reciprocal).map (fun state =>
      let data := GeneralPaperBasisAffineData.prepare state
      let gamma : ℚ := if reciprocal then 1/endpoint else endpoint
      (GeneralPaperBasisAffineEvaluate.atRational data gamma).1)

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    Option (GeneralPaperBasisRationalSolve.RatVector (m*((prepare m k).K-1))) :=
  let endpoint := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  if reciprocal=true ∧ endpoint=0 then none else
    (GeneralPaperSourceBasis.run k Qv hQv weights hp hs b reciprocal).map (fun state =>
      let data := GeneralPaperBasisAffineData.prepare state
      let gamma : ℚ := if reciprocal then 1/endpoint else endpoint
      (GeneralPaperBasisAffineEvaluate.atRational data gamma).1)

theorem prepared_run_source {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    preparedRun k (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal)
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint reciprocal=
        run k Qv hQv weights hp hs b reciprocal := rfl

theorem evaluated_feasible {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h : ℕ) (state : State (m*(K-1)) (m*(K-1))) (hD : state.determinant≠0) (gamma : ℚ)
    (hGood : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h (gamma:ℝ)
      (fun a => GeneralPaperBasisAffineSystem.value (GeneralPaperBasisAffineData.prepare state) (gamma:ℝ) (index a))) :
    GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h (gamma:ℝ)
      (fun a => (GeneralPaperBasisOriginalDirection.reader
        (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1 a:ℝ)) := by
  have hd : (GeneralPaperBasisAffineData.prepare state).determinant≠0 := hD
  simpa only [GeneralPaperBasisOriginalDirection.reader,GeneralPaperBasisAffineEvaluate.rational_real _ hd] using hGood

theorem rich {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false
    ∃ point,run k Qv hQv weights hp hs b false=some point ∧
      GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label
        (score (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S) prep.threshold
        ((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ)
        (fun a => (GeneralPaperBasisOriginalDirection.reader point a:ℝ)) := by
  obtain ⟨state,hRun,inv⟩ := GeneralPaperSourceBasis.run_valid k Qv hm hQv weights hp hs b hb false
  let point := (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state)
    (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).1
  refine ⟨point,?_,?_⟩
  · simp only [run,Bool.false_eq_true,false_and,ite_false,hRun,Option.map_some,point]
  · have hCont := GeneralPaperBasisEndpointContinuation.rich k hm
      (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false).dictionary
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S _ _
      (positive m k hm b hb false).1 _ _ state inv b hb hModify
      (GeneralPaperBasisContinuationControls.auxiliary_value m k hm b hb false)
    exact evaluated_feasible _ _ _ _ state inv.nonzero _ hCont

theorem poor {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hEndpoint : (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
    ∃ point,run k Qv hQv weights hp hs b true=some point ∧
      GeneralPaperAffineConstraintRows.Feasible prep.dictionary.label
        (score (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S) prep.threshold
        (1/((GeneralPaperProxyClassifier.classify m k b).choice.endpoint:ℝ))
        (fun a => (GeneralPaperBasisOriginalDirection.reader point a:ℝ)) := by
  obtain ⟨state,hRun,inv⟩ := GeneralPaperSourceBasis.run_valid k Qv hm hQv weights hp hs b hb true
  let gamma : ℚ := 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
  let point := (GeneralPaperBasisAffineEvaluate.atRational (GeneralPaperBasisAffineData.prepare state) gamma).1
  refine ⟨point,?_,?_⟩
  · have he : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint≠0 := by exact_mod_cast hEndpoint.ne'
    simp only [run,he,and_false,ite_false,ite_true,hRun,Option.map_some,point,gamma]
  · have hCont := GeneralPaperBasisEndpointContinuation.poor k hm
      (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true).dictionary
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S _ _
      (positive m k hm b hb true).1 _ _ state inv b hb hModify hEndpoint
      (GeneralPaperBasisContinuationControls.auxiliary_value m k hm b hb true)
    have hRat : GeneralPaperAffineConstraintRows.Feasible
        (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true).dictionary.label
        (score (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S)
        (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true).threshold (gamma:ℝ)
        (fun a => GeneralPaperBasisAffineSystem.value (GeneralPaperBasisAffineData.prepare state) (gamma:ℝ) (index a)) := by
      simpa only [gamma,Rat.cast_div,Rat.cast_one] using hCont
    have hh := evaluated_feasible _ _ _ _ state inv.nonzero gamma hRat
    simpa only [gamma,Rat.cast_div,Rat.cast_one] using hh

end Blotto.GeneralPaperSourceBasisEndpoint
