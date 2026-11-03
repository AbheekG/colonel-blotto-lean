import Blotto.GeneralPaperEndpointDictionarySize

/-! Actual checked endpoint branches return short literal dictionaries.
The zero-first branch is included; a reciprocal is used only on the
proved-positive poor endpoint path. No source/feasibility/size oracle.
-/
namespace Blotto.GeneralPaperCheckedBranchSize
open GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem rich {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    ∃ result,GeneralPaperCheckedEndpointBranch.run k Qv hQv weights hp hs b false=some result ∧
      GeneralPaperEndpointDictionarySize.Contract k result := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b false
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  by_cases hMax : prep.threshold=GeneralPaperScoreMaximum.run (K := (prepare m k).K)
      (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  · refine ⟨⟨prep.dictionary.label,.zero⟩,?_,GeneralPaperEndpointDictionarySize.zero k _⟩
    dsimp only [prep,v] at hMax
    simp only [GeneralPaperCheckedEndpointBranch.run,hMax,ite_true,prep]
  · obtain ⟨point,D,hRun,hc⟩ := GeneralPaperSourceEndpointSize.rich k Qv hm hQv weights hp hs b hb hModify
    refine ⟨⟨prep.dictionary.label,.endpoint (GeneralPaperProxyClassifier.classify m k b).choice.endpoint point⟩,?_,
      GeneralPaperEndpointDictionarySize.endpoint k _ _ _ D hc⟩
    dsimp only [prep,v] at hMax
    simp only [GeneralPaperCheckedEndpointBranch.run,hMax,ite_false,GeneralPaperCheckedSourceEndpoint.prepared_run_source,
      hRun,Option.map_some,prep,Bool.false_eq_true]

theorem poor {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    ∃ result,GeneralPaperCheckedEndpointBranch.run k Qv hQv weights hp hs b true=some result ∧
      GeneralPaperEndpointDictionarySize.Contract k result := by
  let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b true
  let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
  have hMaxData := GeneralPaperScoreMaximum.run_data (K := (prepare m k).K)
    (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
  by_cases hMax : prep.threshold=GeneralPaperScoreMaximum.run (K := (prepare m k).K)
      (GeneralPaperScoreScaleParameters.prepare m k).depth v (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k)
  · refine ⟨⟨prep.dictionary.label,.zero⟩,?_,GeneralPaperEndpointDictionarySize.zero k _⟩
    dsimp only [prep,v] at hMax
    simp only [GeneralPaperCheckedEndpointBranch.run,hMax,ite_true,prep]
  · have hNonmaximal : prep.threshold≠GeneralPaperScoreMaximum.maximum v (prepare m k).S := by
      simpa only [hMaxData] using hMax
    have hPositive := GeneralPaperSourcePoorZero.endpoint_positive_of_nonmaximal k Qv hm hQv weights hp hs b hb hModify hNonmaximal
    obtain ⟨point,D,hRun,hc⟩ := GeneralPaperSourceEndpointSize.poor k Qv hm hQv weights hp hs b hb hModify hPositive
    refine ⟨⟨prep.dictionary.label,.endpoint (1/(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) point⟩,?_,
      GeneralPaperEndpointDictionarySize.endpoint k _ _ _ D hc⟩
    dsimp only [prep,v] at hMax
    simp only [GeneralPaperCheckedEndpointBranch.run,hMax,ite_false,ite_true,GeneralPaperCheckedSourceEndpoint.prepared_run_source,
      hRun,Option.map_some,prep]

theorem rich_modified {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .rich) :
    ∃ d,GeneralPaperCheckedSourcePair.modified k Qv hQv weights hp hs b false=some d ∧
      ∀ j l,RationalHeight (d.anchor j l) (GeneralPaperEndpointDictionarySize.width m k) := by
  obtain ⟨result,hr,hc⟩ := rich k Qv hm hQv weights hp hs b hb hModify
  refine ⟨GeneralPaperEndpointDictionary.dictionary result,?_,hc.1⟩
  simp only [GeneralPaperCheckedSourcePair.modified,hr,Option.map_some]

theorem poor_modified {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor) :
    ∃ d,GeneralPaperCheckedSourcePair.modified k Qv hQv weights hp hs b true=some d ∧
      ∀ j l,RationalHeight (d.anchor j l) (GeneralPaperEndpointDictionarySize.width m k) := by
  obtain ⟨result,hr,hc⟩ := poor k Qv hm hQv weights hp hs b hb hModify
  refine ⟨GeneralPaperEndpointDictionary.dictionary result,?_,hc.1⟩
  simp only [GeneralPaperCheckedSourcePair.modified,hr,Option.map_some]

end Blotto.GeneralPaperCheckedBranchSize
