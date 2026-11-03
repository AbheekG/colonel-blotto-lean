import Blotto.GeneralPaperRetainedCompilerBranch

/-! The retained arithmetic compiler branch is the actual selected
source's checked branch. Its physical-column and stored-value premises
are erased data equalities, discharged by the native source/value joins.
The data path calls neither the canonical source nor its compiler again. -/
namespace Blotto.GeneralPaperRetainedCompilerSource
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem prepared {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    (GeneralPaperRetainedTransferPreparation.run false model 1 (GeneralPaperScoreScaleParameters.prepare m k).depth
      (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)).1.prepared=
        GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal := by
  erw [GeneralPaperRetainedTransferPreparation.data (K := (prepare m k).K) false model 1
    (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values _ _ (GeneralPaperScoreScaleParameters.score_cap m k),
    hColumns,hValues]
  rfl

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (endpoint : Farey.Fraction) (hEndpoint : endpoint.value=(GeneralPaperProxyClassifier.classify m k b).choice.endpoint) :
    (GeneralPaperRetainedCompilerBranch.run model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (prepare m k).H (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
      (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint).1=
        GeneralPaperCheckedEndpointBranch.run k Qv hQv weights hp hs b reciprocal := by
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hn := GeneralPaperRetainedCompilerBranch.data model k
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.num
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint
    (GeneralPaperProxyClassifier.classify m k b).choice.endpoint hEndpoint hm hf.1
    (GeneralPaperProxyClassifier.classify m k b).choice.proxy.den_pos
  dsimp only at hn
  erw [prepared model k Qv hQv weights hp hs b reciprocal columns values hColumns hValues,hValues] at hn
  have hMax := GeneralPaperScoreMaximum.run_data (K := (prepare m k).K)
    (GeneralPaperScoreScaleParameters.prepare m k).depth (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperScoreScaleParameters.score_cap m k)
  refine hn.trans ?_
  simp only [GeneralPaperCheckedEndpointBranch.run,hMax]

end Blotto.GeneralPaperRetainedCompilerSource
