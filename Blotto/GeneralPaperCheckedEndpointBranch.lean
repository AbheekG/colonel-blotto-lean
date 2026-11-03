import Blotto.GeneralPaperCheckedSourceEndpoint
import Blotto.GeneralPaperSourceEndpointBranch

/-! The selected endpoint branch executes both final checks. The maximum
score test still precedes basis construction and reciprocal evaluation.
The source preparation is shared with the checked basis compiler.
-/
namespace Blotto.GeneralPaperCheckedEndpointBranch
open GeneralPaperProxyParameters GeneralPaperSourceEndpointBranch
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    Option (Result (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K) :=
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
  let maximum := GeneralPaperScoreMaximum.run (K := (prepare m k).K) (GeneralPaperScoreScaleParameters.prepare m k).depth
    (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  if prep.threshold=maximum then some ⟨prep.dictionary.label,.zero⟩ else
    (GeneralPaperCheckedBasisEndpoint.run k prep
      (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint reciprocal).map (fun point =>
      let endpoint := (GeneralPaperProxyClassifier.classify m k b).choice.endpoint
      ⟨prep.dictionary.label,.endpoint (if reciprocal then 1/endpoint else endpoint) point⟩)

theorem rich_eq {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    run k Qv hQv weights hp hs b false=GeneralPaperSourceEndpointBranch.run k Qv hQv weights hp hs b false := by
  simp only [run,GeneralPaperSourceEndpointBranch.run,GeneralPaperCheckedSourceEndpoint.prepared_run_source,
    GeneralPaperSourceBasisEndpoint.prepared_run_source,GeneralPaperCheckedSourceEndpoint.rich_eq k Qv hm hQv weights hp hs b hb hModify]

theorem poor_eq {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    run k Qv hQv weights hp hs b true=GeneralPaperSourceEndpointBranch.run k Qv hQv weights hp hs b true := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  have hMaxData := GeneralPaperScoreMaximum.run_data (K := (prepare m k).K)
    (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
  by_cases hMax : prep.threshold=GeneralPaperScoreMaximum.run (K := (prepare m k).K)
      (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  · dsimp only [prep,v] at hMax
    simp only [run,GeneralPaperSourceEndpointBranch.run,hMax,ite_true]
  · have hNonmaximal : prep.threshold≠GeneralPaperScoreMaximum.maximum v (prepare m k).S := by
      simpa only [hMaxData] using hMax
    have hPositive := GeneralPaperSourcePoorZero.endpoint_positive_of_nonmaximal k Qv hm hQv weights hp hs b hb hModify hNonmaximal
    simp only [run,GeneralPaperSourceEndpointBranch.run,GeneralPaperCheckedSourceEndpoint.prepared_run_source,
      GeneralPaperSourceBasisEndpoint.prepared_run_source,GeneralPaperCheckedSourceEndpoint.poor_eq k Qv hm hQv weights hp hs b hb hModify hPositive]

end Blotto.GeneralPaperCheckedEndpointBranch
