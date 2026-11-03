import Blotto.GeneralPaperRetainedModifiedSource

/-! Decode the retained compiler's actual rich/poor arrays to the selected
source pair. The unchanged paths retain arrays directly, while precisely
one modified path invokes the full compiler. All continuous/security facts
belong to the resulting literal source pair, not to a marginal surrogate. -/
namespace Blotto.GeneralPaperRetainedPairSource
open GeneralPaperProxyParameters GeneralPaperOriginalDrawEquilibrium
open GeneralPaperSourcePairRun
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (columns : Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hRich : GeneralPaperRowQuantizer.dictionary columns.rich=GeneralPaperSourceUnchangedDictionary.run k Qv weights b false)
    (hPoor : GeneralPaperRowQuantizer.dictionary columns.poor=GeneralPaperSourceUnchangedDictionary.run k Qv weights b true)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    (GeneralPaperRetainedCompilerPair.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
      (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value values columns).1.map
        GeneralPaperPhysicalColumnPair.decode=GeneralPaperCheckedSourcePair.run k Qv hQv weights hp hs b := by
  have hEndpoint := GeneralPaperRetainedEndpointFraction.actual_value (fun _ => 1) 1 m k b
  have hr := GeneralPaperRetainedModifiedSource.data model k Qv hm hQv weights hp hs b hb false columns.rich values hRich hValues _ hEndpoint
  have hp' := GeneralPaperRetainedModifiedSource.data model k Qv hm hQv weights hp hs b hb true columns.poor values hPoor hValues _ hEndpoint
  cases hc : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none =>
    simp only [GeneralPaperRetainedCompilerPair.run,GeneralPaperCheckedSourcePair.run,hc]
    dsimp only [Option.map,GeneralPaperPhysicalColumnPair.decode]
    erw [hRich,hPoor]
    rfl
  | some side =>
    cases side with
    | rich =>
      simp only [GeneralPaperRetainedCompilerPair.run,GeneralPaperCheckedSourcePair.run,hc]
      erw [GeneralPaperPhysicalColumnPair.rich_map,hPoor]
      exact congrArg (Option.map (fun d =>
        (⟨d,GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩ : Pair
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K))) hr
    | poor =>
      simp only [GeneralPaperRetainedCompilerPair.run,GeneralPaperCheckedSourcePair.run,hc]
      erw [GeneralPaperPhysicalColumnPair.poor_map,hRich]
      exact congrArg (Option.map (fun d =>
        (⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,d⟩ : Pair
          (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K))) hp'

theorem actual_return {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (columns : Columns (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K)
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hRich : GeneralPaperRowQuantizer.dictionary columns.rich=GeneralPaperSourceUnchangedDictionary.run k Qv weights b false)
    (hPoor : GeneralPaperRowQuantizer.dictionary columns.poor=GeneralPaperSourceUnchangedDictionary.run k Qv weights b true)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    ∃ physical pair,
      (GeneralPaperRetainedCompilerPair.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
        (prepare m k).H (prepare m k).Qg (grid_positive m k) (GeneralPaperScoreScaleParameters.labels_positive m k)
        (GeneralPaperProxyClassifier.classify m k b) (GeneralPaperProxyClassifier.classify m k b).choice.proxy.value values columns).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hs b=some pair ∧ Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair := by
  obtain ⟨pair,hPair,hContract⟩ := GeneralPaperCheckedSourcePair.run_contract k Qv hm hQv weights hp hs b hb
  have hd := data model k Qv hm hQv weights hp hs b hb columns values hRich hPoor hValues
  erw [hPair] at hd
  obtain ⟨physical,hRun,hDecode⟩ := Option.map_eq_some_iff.mp hd
  refine ⟨physical,pair,hRun,?_,(GeneralPaperPhysicalColumnPair.matches_iff physical pair).mpr hDecode,hContract⟩
  exact (GeneralPaperCheckedSourcePair.run_eq k Qv hm hQv weights hp hs b hb).symm.trans hPair

end Blotto.GeneralPaperRetainedPairSource
