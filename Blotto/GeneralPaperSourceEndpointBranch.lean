import Blotto.GeneralPaperSourcePoorZero

/-! The actual modified-defender endpoint branch: test the computed
maximum score first, return an all-zero dictionary tag immediately when
it is attained, otherwise evaluate the full original basis. Original
whole-row labels are retained in either case. No zero reciprocal is run.
-/
namespace Blotto.GeneralPaperSourceEndpointBranch
open RationalOrderCell GeneralPaperStrictScore GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

inductive Choice (d : ℕ) where
  | zero
  | endpoint (gamma : ℚ) (point : GeneralPaperBasisRationalSolve.RatVector d)

structure Result (T m K : ℕ) where
  labels : Fin T → Fin m → Fin K
  choice : Choice (m*(K-1))

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    Option (Result (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K) :=
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let maximum := GeneralPaperScoreMaximum.run (K := (prepare m k).K) (GeneralPaperScoreScaleParameters.prepare m k).depth
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  if prep.threshold=maximum then some ⟨prep.dictionary.label,.zero⟩ else
    (GeneralPaperSourceBasisEndpoint.preparedRun k prep
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint reciprocal).map (fun point =>
      let endpoint := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      ⟨prep.dictionary.label,.endpoint (if reciprocal then 1/endpoint else endpoint) point⟩)

noncomputable def Contract {T m K : ℕ} (old : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h : ℕ) (budget : ℝ) (result : Result T m K) : Prop :=
  result.labels=old.label ∧ match result.choice with
    | .zero => ∀ labels : Fin m → Fin K,totalScore v S labels≤h
    | .endpoint gamma point => budget<(gamma:ℝ) ∧
      GeneralPaperAffineConstraintRows.Feasible result.labels (score v S) h (gamma:ℝ)
        (fun a => (GeneralPaperBasisOriginalDirection.reader point a:ℝ))

theorem rich {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false
    ∃ result,run k Qv hQv weights hp hs b false=some result ∧
      Contract prep.dictionary (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S prep.threshold b result := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  have hMaxData := GeneralPaperScoreMaximum.run_data (K := (prepare m k).K)
    (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
  by_cases hMax : prep.threshold=GeneralPaperScoreMaximum.run (K := (prepare m k).K)
      (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  · refine ⟨⟨prep.dictionary.label,.zero⟩,?_,rfl,?_⟩
    · have hMax' := hMax
      dsimp only [prep,v] at hMax'
      simp only [run,hMax',ite_true,prep]
    · intro labels
      rw [hMax,hMaxData]
      exact GeneralPaperScoreMaximum.total_le v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) labels
  · obtain ⟨point,hRun,hGood⟩ := GeneralPaperSourceBasisEndpoint.rich k Qv hm hQv weights hp hs b hb hModify
    refine ⟨⟨prep.dictionary.label,.endpoint (GeneralPaperProxyClassifier.classify m k b).choice.endpoint point⟩,?_,rfl,?_,hGood⟩
    · have hMax' := hMax
      dsimp only [prep,v] at hMax'
      simp only [run,hMax',ite_false,GeneralPaperSourceBasisEndpoint.prepared_run_source,hRun,Option.map_some,prep,Bool.false_eq_true]
    · exact (GeneralPaperProxyClassifierPaths.rich_direction m k b hb hModify).2

theorem poor {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
    ∃ result,run k Qv hQv weights hp hs b true=some result ∧
      Contract prep.dictionary (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S prep.threshold (1/b) result := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  have hMaxData := GeneralPaperScoreMaximum.run_data (K := (prepare m k).K)
    (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
  by_cases hMax : prep.threshold=GeneralPaperScoreMaximum.run (K := (prepare m k).K)
      (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  · refine ⟨⟨prep.dictionary.label,.zero⟩,?_,rfl,?_⟩
    · have hMax' := hMax
      dsimp only [prep,v] at hMax'
      simp only [run,hMax',ite_true,prep]
    · intro labels
      rw [hMax,hMaxData]
      exact GeneralPaperScoreMaximum.total_le v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) labels
  · have hNonmaximal : prep.threshold≠GeneralPaperScoreMaximum.maximum v (prepare m k).S := by
      simpa only [hMaxData] using hMax
    have hPositive := GeneralPaperSourcePoorZero.endpoint_positive_of_nonmaximal k Qv hm hQv weights hp hs b hb hModify hNonmaximal
    obtain ⟨point,hRun,hGood⟩ := GeneralPaperSourceBasisEndpoint.poor k Qv hm hQv weights hp hs b hb hModify hPositive
    let gamma : ℚ := 1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint
    refine ⟨⟨prep.dictionary.label,.endpoint gamma point⟩,?_,rfl,?_⟩
    · have hMax' := hMax
      dsimp only [prep,v] at hMax'
      simp only [run,hMax',ite_false,ite_true,GeneralPaperSourceBasisEndpoint.prepared_run_source,hRun,Option.map_some,gamma,prep]
    · have hd := (GeneralPaperProxyClassifierPaths.poor_reciprocal_direction m k b hb hModify hPositive).2
      simpa only [gamma,Rat.cast_div,Rat.cast_one] using And.intro hd hGood

end Blotto.GeneralPaperSourceEndpointBranch
